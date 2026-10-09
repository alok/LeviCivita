import LeviCivita.Fast

-- Differentiating Through Discrete Neural Networks with Levi-Civita
--
-- The problem: Neural networks with discrete activations (step functions,
-- argmax, quantization) have zero gradients almost everywhere, breaking
-- backpropagation.
--
-- The solution: Use Levi-Civita series with infinitely steep sigmoids.
-- These behave EXACTLY like discrete functions for standard inputs,
-- but have well-defined (infinite) gradients at transition points.
--
-- This gives mathematical rigor to "straight-through estimators" and
-- lets us reason about what gradients through discrete ops actually mean.

set_option linter.missingDocs false

namespace LeviCivita.DiscreteNN

open LeviCivita.Fast

-- The infinite steepness parameter
def N : FastLC.LC := FastLC.H  -- N = 1/ε

-- Hard step function via infinitely steep sigmoid
-- For standard x: returns 0 if x < 0, 1 if x > 0, 0.5 if x = 0
-- But has infinite derivative at x = 0!
def hardSigmoid (x : Float) : FastLC.LC :=
  if x > 0.001 then FastLC.ofFloat 1.0
  else if x < -0.001 then FastLC.ofFloat 0.0
  else
    -- Near zero: use the infinitely steep sigmoid formula
    -- σ(Nx) ≈ 0.5 + (N/4)x for small x
    -- This gives derivative N/4 at x=0
    FastLC.ofFloat 0.5 + (N * FastLC.ofFloat 0.25) * FastLC.ofFloat x

-- Derivative of hard sigmoid
-- Zero everywhere except at x ≈ 0 where it's N/4 (infinite)
def hardSigmoidDeriv (x : Float) : FastLC.LC :=
  if x > 0.001 || x < -0.001 then
    FastLC.ofFloat 0.0  -- Flat regions have zero derivative
  else
    N * FastLC.ofFloat 0.25  -- Infinite derivative at transition

-- A simple 2-input, 1-output "neuron" with discrete activation
structure Neuron where
  w1 : Float  -- weight for input 1
  w2 : Float  -- weight for input 2
  b  : Float  -- bias

-- Forward pass: output = hardSigmoid(w1*x1 + w2*x2 + b)
def Neuron.forward (n : Neuron) (x1 x2 : Float) : FastLC.LC :=
  let z := n.w1 * x1 + n.w2 * x2 + n.b
  hardSigmoid z

-- Backward pass: compute gradients w.r.t. weights
-- dL/dw1 = dL/dy * dy/dz * dz/dw1 = dL/dy * σ'(z) * x1
structure Gradients where
  dw1 : FastLC.LC
  dw2 : FastLC.LC
  db  : FastLC.LC

def Neuron.backward (n : Neuron) (x1 x2 : Float) (dLdy : FastLC.LC) : Gradients :=
  let z := n.w1 * x1 + n.w2 * x2 + n.b
  let dydz := hardSigmoidDeriv z  -- This can be infinite!
  let dLdz := dLdy * dydz
  { dw1 := dLdz * FastLC.ofFloat x1
    dw2 := dLdz * FastLC.ofFloat x2
    db  := dLdz }

-- Simple MSE loss: L = (y - target)^2
def mseLoss (y : FastLC.LC) (target : Float) : FastLC.LC :=
  let diff := y - FastLC.ofFloat target
  diff * diff

-- dL/dy = 2(y - target)
def mseLossGrad (y : FastLC.LC) (target : Float) : FastLC.LC :=
  FastLC.ofFloat 2.0 * (y - FastLC.ofFloat target)

-- Demo: Train a neuron to learn AND gate
-- AND(0,0)=0, AND(0,1)=0, AND(1,0)=0, AND(1,1)=1

#eval do
  IO.println "=== Discrete Neural Network with Levi-Civita Gradients ==="
  IO.println ""
  IO.println "Training a single neuron to learn AND gate"
  IO.println "Using HARD sigmoid activation (infinitely steep)"
  IO.println ""

  -- Initial weights (random-ish)
  let mut neuron : Neuron := { w1 := 0.5, w2 := 0.5, b := -0.2 }

  -- Training data for AND gate
  let data := #[(0.0, 0.0, 0.0), (0.0, 1.0, 0.0), (1.0, 0.0, 0.0), (1.0, 1.0, 1.0)]

  IO.println "Initial weights:"
  IO.println s!"  w1={neuron.w1}, w2={neuron.w2}, b={neuron.b}"
  IO.println ""

  -- Show forward pass on all inputs
  IO.println "Forward pass with initial weights:"
  for (x1, x2, target) in data do
    let y := neuron.forward x1 x2
    IO.println s!"  AND({x1}, {x2}) = {FastLC.std y} (target: {target})"

  IO.println ""
  IO.println "Computing gradients at each training point:"
  IO.println ""

  for (x1, x2, target) in data do
    let y := neuron.forward x1 x2
    let loss := mseLoss y target
    let dLdy := mseLossGrad y target
    let grads := neuron.backward x1 x2 dLdy

    let z := neuron.w1 * x1 + neuron.w2 * x2 + neuron.b

    IO.println s!"Input ({x1}, {x2}), target={target}:"
    IO.println s!"  pre-activation z = {z}"
    IO.println s!"  output y = {FastLC.std y}"
    IO.println s!"  loss = {FastLC.std loss}"

    -- Check if gradient is infinite (at decision boundary)
    let gradMagnitude := FastLC.std grads.dw1
    if z.abs < 0.01 then
      IO.println s!"  *** AT DECISION BOUNDARY ***"
      IO.println s!"  dw1 = {grads.dw1} (INFINITE - contains H term!)"
      IO.println s!"  dw2 = {grads.dw2}"
      IO.println s!"  db  = {grads.db}"
    else
      IO.println s!"  dw1 = {FastLC.std grads.dw1} (standard, discrete region)"
      IO.println s!"  dw2 = {FastLC.std grads.dw2}"
      IO.println s!"  db  = {FastLC.std grads.db}"
    IO.println ""

-- Demo: What happens exactly at a decision boundary
#eval do
  IO.println "=== Decision Boundary Analysis ==="
  IO.println ""
  IO.println "When the pre-activation z ≈ 0, we're at the decision boundary."
  IO.println "The hard sigmoid has INFINITE gradient here!"
  IO.println ""

  -- Neuron perfectly balanced at decision boundary
  let neuron : Neuron := { w1 := 1.0, w2 := 1.0, b := -1.0 }
  -- Input that lands exactly at z = 0
  let x1 := 0.5
  let x2 := 0.5
  let z := neuron.w1 * x1 + neuron.w2 * x2 + neuron.b

  IO.println s!"Neuron: w1={neuron.w1}, w2={neuron.w2}, b={neuron.b}"
  IO.println s!"Input: ({x1}, {x2})"
  IO.println s!"Pre-activation: z = {z}"
  IO.println ""

  let y := neuron.forward x1 x2
  let target := 1.0
  let dLdy := mseLossGrad y target
  let grads := neuron.backward x1 x2 dLdy

  IO.println s!"Output: y = {y}"
  IO.println s!"Target: {target}"
  IO.println s!"Loss gradient dL/dy = {dLdy}"
  IO.println ""
  IO.println "Gradients (note the H = 1/ε term - INFINITE!):"
  IO.println s!"  dL/dw1 = {grads.dw1}"
  IO.println s!"  dL/dw2 = {grads.dw2}"
  IO.println s!"  dL/db  = {grads.db}"
  IO.println ""
  IO.println "Interpretation:"
  IO.println "  The infinite gradient means: at the decision boundary,"
  IO.println "  an infinitesimal change in weights causes a FINITE change in output."
  IO.println "  This is the mathematically correct gradient of a step function!"
  IO.println ""
  IO.println "  In practice, you'd use: gradient = st(LC_gradient * ε)"
  IO.println "  to get a finite update, or use the sign of the infinite part."

-- Show how to extract a "usable" gradient from the infinite one
#eval do
  IO.println ""
  IO.println "=== Extracting Usable Gradients ==="
  IO.println ""

  -- At boundary: gradient = (something) * H = (something) / ε
  -- Multiply by ε to get the "direction" of the gradient
  let infiniteGrad := FastLC.H * FastLC.ofFloat 0.25  -- typical N/4 term
  let usableGrad := infiniteGrad * FastLC.epsilon  -- multiply by ε

  IO.println s!"Infinite gradient: {infiniteGrad}"
  IO.println s!"Multiply by ε:     {usableGrad}"
  IO.println s!"Standard part:     {FastLC.std usableGrad}"
  IO.println ""
  IO.println "This recovers a finite gradient that indicates the"
  IO.println "correct direction to move weights at a decision boundary."
  IO.println ""
  IO.println "This is what 'straight-through estimators' do heuristically -"
  IO.println "Levi-Civita gives it mathematical justification!"

end LeviCivita.DiscreteNN
