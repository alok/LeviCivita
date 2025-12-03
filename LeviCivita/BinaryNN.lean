import LeviCivita.Fast

-- Binary Neural Networks with Levi-Civita Gradients
--
-- Binarized Neural Networks (BNNs) use:
--   - Binary weights: +1 or -1
--   - Binary activations: sign(x)
--
-- Problem: sign(x) has zero gradient everywhere except x=0.
-- Traditional solution: "Straight-through estimator" (STE) - a heuristic.
--
-- Our solution: Levi-Civita gives EXACT gradients through discrete ops.
-- The gradient is infinite at transitions, but we can extract useful info.
--
-- This demonstrates training a BNN on a digit classification task.

set_option linter.missingDocs false

namespace LeviCivita.BinaryNN

open LeviCivita.Fast

-- Infinite steepness for hard functions
def N : FastLC.LC := FastLC.H

-- Hard sign function: returns -1 if x < 0, +1 if x > 0
-- At x = 0, returns 0 and has infinite derivative
def hardSign (x : Float) : FastLC.LC :=
  if x > 0.001 then FastLC.ofFloat 1.0
  else if x < -0.001 then FastLC.ofFloat (-1.0)
  else
    -- At boundary: linear with infinite slope
    -- sign(x) ≈ (N/2) * x for small x, clamped to [-1, 1]
    N * FastLC.ofFloat 0.5 * FastLC.ofFloat x

-- Derivative of hard sign: 0 everywhere except at x ≈ 0 where it's N/2
def hardSignDeriv (x : Float) : FastLC.LC :=
  if x.abs > 0.001 then FastLC.ofFloat 0.0
  else N * FastLC.ofFloat 0.5

-- Binarize weights: snap to +1 or -1
def binarize (w : Float) : Float :=
  if w >= 0.0 then 1.0 else -1.0

-- A small "image" - 4x4 = 16 pixels, values in [-1, 1]
abbrev Image := Array Float  -- length 16

-- Simple patterns for digits 0-3 (4x4 bitmaps)
-- Using +1 for white, -1 for black
def digit0 : Image := #[
  -1,  1,  1, -1,
   1, -1, -1,  1,
   1, -1, -1,  1,
  -1,  1,  1, -1
]

def digit1 : Image := #[
  -1,  1, -1, -1,
   1,  1, -1, -1,
  -1,  1, -1, -1,
   1,  1,  1, -1
]

def digit2 : Image := #[
   1,  1,  1, -1,
  -1, -1,  1, -1,
  -1,  1, -1, -1,
   1,  1,  1, -1
]

def digit3 : Image := #[
   1,  1,  1, -1,
  -1, -1,  1, -1,
  -1,  1,  1, -1,
   1,  1,  1, -1
]

-- Binary Neural Network: 16 inputs -> 8 hidden -> 4 outputs
-- Real weights are stored, binarized during forward pass
structure BNN where
  -- Layer 1: 16 -> 8
  w1 : Array Float  -- 8 * 16 = 128 weights
  b1 : Array Float  -- 8 biases
  -- Layer 2: 8 -> 4
  w2 : Array Float  -- 4 * 8 = 32 weights
  b2 : Array Float  -- 4 biases

-- Initialize with small random-ish weights
def BNN.init : BNN := {
  w1 := Array.range 128 |>.map fun i =>
    (Float.sin (i.toFloat * 0.7)) * 0.5
  b1 := #[0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
  w2 := Array.range 32 |>.map fun i =>
    (Float.cos (i.toFloat * 0.9)) * 0.5
  b2 := #[0.0, 0.0, 0.0, 0.0]
}

-- Forward pass with binarized weights and hard sign activation
-- Returns (hidden_pre, hidden_post, output_pre, output)
def BNN.forward (net : BNN) (input : Image) :
    Array Float × Array FastLC.LC × Array Float × Array FastLC.LC := Id.run do
  -- Layer 1: binary weights, hard sign activation
  let mut hidden_pre : Array Float := #[]
  let mut hidden_post : Array FastLC.LC := #[]

  for h in [:8] do
    let mut sum : Float := net.b1[h]!
    for i in [:16] do
      let w := binarize net.w1[h * 16 + i]!  -- Binarize weight
      sum := sum + w * input[i]!
    hidden_pre := hidden_pre.push sum
    hidden_post := hidden_post.push (hardSign sum)  -- Hard activation

  -- Layer 2: binary weights, output logits
  let mut output_pre : Array Float := #[]
  let mut output : Array FastLC.LC := #[]

  for o in [:4] do
    let mut sum : Float := net.b2[o]!
    for h in [:8] do
      let w := binarize net.w2[o * 8 + h]!
      sum := sum + w * (FastLC.std hidden_post[h]!)
    output_pre := output_pre.push sum
    output := output.push (hardSign sum)  -- Hard activation for classification

  (hidden_pre, hidden_post, output_pre, output)

-- Compute gradients w.r.t. real weights (not binary weights)
-- This is where Levi-Civita shines!
structure Gradients where
  dw1 : Array FastLC.LC
  db1 : Array FastLC.LC
  dw2 : Array FastLC.LC
  db2 : Array FastLC.LC

-- Simple loss: -1 if correct class has highest activation, else 1
def classificationLoss (output : Array FastLC.LC) (label : Nat) : FastLC.LC :=
  let target := output[label]!
  -- Want target to be +1, others to be -1
  FastLC.ofFloat 1.0 - target

-- Backward pass - compute gradients through hard activations
def BNN.backward (net : BNN) (input : Image) (label : Nat) : Gradients := Id.run do
  let (hidden_pre, hidden_post, output_pre, _) := net.forward input

  -- Output layer gradients
  -- dL/d(output[label]) = -1
  let mut dL_dOutput : Array FastLC.LC := #[0, 0, 0, 0].map FastLC.ofFloat
  dL_dOutput := dL_dOutput.set! label (FastLC.ofFloat (-1.0))

  -- Gradient through output hardSign
  let mut dL_dOutputPre : Array FastLC.LC := #[]
  for o in [:4] do
    let grad := hardSignDeriv output_pre[o]!
    dL_dOutputPre := dL_dOutputPre.push (dL_dOutput[o]! * grad)

  -- Layer 2 weight gradients
  let mut dw2 : Array FastLC.LC := #[]
  for _ in [:32] do dw2 := dw2.push 0
  let mut db2 : Array FastLC.LC := #[]
  for _ in [:4] do db2 := db2.push 0

  for o in [:4] do
    db2 := db2.set! o dL_dOutputPre[o]!
    for h in [:8] do
      let grad := dL_dOutputPre[o]! * hidden_post[h]!
      dw2 := dw2.set! (o * 8 + h) grad

  -- Backprop to hidden layer
  let mut dL_dHiddenPost : Array FastLC.LC := #[]
  for _ in [:8] do dL_dHiddenPost := dL_dHiddenPost.push 0
  for h in [:8] do
    let mut sum : FastLC.LC := 0
    for o in [:4] do
      let w := binarize net.w2[o * 8 + h]!
      sum := sum + dL_dOutputPre[o]! * FastLC.ofFloat w
    dL_dHiddenPost := dL_dHiddenPost.set! h sum

  -- Gradient through hidden hardSign
  let mut dL_dHiddenPre : Array FastLC.LC := #[]
  for h in [:8] do
    let grad := hardSignDeriv hidden_pre[h]!
    dL_dHiddenPre := dL_dHiddenPre.push (dL_dHiddenPost[h]! * grad)

  -- Layer 1 weight gradients
  let mut dw1 : Array FastLC.LC := #[]
  for _ in [:128] do dw1 := dw1.push 0
  let mut db1 : Array FastLC.LC := #[]
  for _ in [:8] do db1 := db1.push 0

  for h in [:8] do
    db1 := db1.set! h dL_dHiddenPre[h]!
    for i in [:16] do
      let grad := dL_dHiddenPre[h]! * FastLC.ofFloat input[i]!
      dw1 := dw1.set! (h * 16 + i) grad

  { dw1, db1, dw2, db2 }

-- Extract usable gradient from LC (multiply infinite part by ε)
def extractGrad (g : FastLC.LC) : Float :=
  -- If gradient has H term (infinite), multiply by ε to get direction
  -- Otherwise use standard part
  let scaled := g * FastLC.epsilon
  let result := FastLC.std scaled
  if result != 0.0 then result
  else FastLC.std g

-- Update weights using extracted gradients
def BNN.update (net : BNN) (grads : Gradients) (lr : Float) : BNN := Id.run do
  let mut w1 := net.w1
  for i in [:w1.size] do
    w1 := w1.set! i (w1[i]! - lr * extractGrad grads.dw1[i]!)
  let mut b1 := net.b1
  for i in [:b1.size] do
    b1 := b1.set! i (b1[i]! - lr * extractGrad grads.db1[i]!)
  let mut w2 := net.w2
  for i in [:w2.size] do
    w2 := w2.set! i (w2[i]! - lr * extractGrad grads.dw2[i]!)
  let mut b2 := net.b2
  for i in [:b2.size] do
    b2 := b2.set! i (b2[i]! - lr * extractGrad grads.db2[i]!)
  { w1, b1, w2, b2 }

-- Predict class (argmax of output)
def BNN.predict (net : BNN) (input : Image) : Nat := Id.run do
  let (_, _, _, output) := net.forward input
  let mut best := 0
  let mut bestVal := FastLC.std output[0]!
  for i in [1:4] do
    let val := FastLC.std output[i]!
    if val > bestVal then
      best := i
      bestVal := val
  best

-- Training data
def trainingData : Array (Image × Nat) := #[
  (digit0, 0), (digit1, 1), (digit2, 2), (digit3, 3)
]

-- Evaluate accuracy
def BNN.accuracy (net : BNN) : Float := Id.run do
  let mut correct := 0
  for (img, label) in trainingData do
    if net.predict img == label then
      correct := correct + 1
  correct.toFloat / trainingData.size.toFloat

#eval do
  IO.println "╔════════════════════════════════════════════════════════════════╗"
  IO.println "║  Binary Neural Network Training with Levi-Civita Gradients    ║"
  IO.println "╠════════════════════════════════════════════════════════════════╣"
  IO.println "║  Architecture: 16 -> 8 -> 4 (all binary weights & activations)║"
  IO.println "║  Task: Classify 4x4 digit patterns (0, 1, 2, 3)                ║"
  IO.println "╚════════════════════════════════════════════════════════════════╝"
  IO.println ""

  let mut net := BNN.init

  IO.println s!"Initial accuracy: {net.accuracy * 100}%"
  IO.println ""

  -- Show initial predictions
  IO.println "Initial predictions:"
  for (img, label) in trainingData do
    let pred := net.predict img
    let (_, _, _, output) := net.forward img
    let outputs := output.map FastLC.std
    IO.println s!"  Digit {label}: predicted {pred}, outputs={outputs.toList}"
  IO.println ""

  -- Training loop
  IO.println "Training with Levi-Civita gradients..."
  IO.println "(Infinite gradients at decision boundaries give learning signal!)"
  IO.println ""

  let lr := 0.1

  for epoch in [:20] do
    let mut totalLoss : Float := 0.0
    let mut infiniteGrads := 0

    for (img, label) in trainingData do
      let grads := net.backward img label

      -- Count infinite gradients (those with H component)
      for g in grads.dw1 do
        if (g * FastLC.epsilon).terms.size > 0 then
          infiniteGrads := infiniteGrads + 1

      net := net.update grads lr

      let (_, _, _, output) := net.forward img
      totalLoss := totalLoss + FastLC.std (classificationLoss output label)

    if epoch % 5 == 0 || epoch == 19 then
      IO.println s!"Epoch {epoch}: loss={totalLoss/4.0}, accuracy={net.accuracy * 100}%, infinite_grads={infiniteGrads}"

  IO.println ""
  IO.println "Final predictions:"
  for (img, label) in trainingData do
    let pred := net.predict img
    let (_, _, _, output) := net.forward img
    let outputs := output.map FastLC.std
    let correct := if pred == label then "✓" else "✗"
    IO.println s!"  Digit {label}: predicted {pred} {correct}, outputs={outputs.toList}"

  IO.println ""
  IO.println s!"Final accuracy: {net.accuracy * 100}%"

-- Detailed gradient analysis for one example
#eval do
  IO.println ""
  IO.println "═══ Gradient Analysis for Digit 0 ═══"
  IO.println ""

  let net := BNN.init
  let grads := net.backward digit0 0

  -- Find gradients with infinite components
  IO.println "Layer 2 weight gradients (showing first 8):"
  for i in [:8] do
    let g := grads.dw2[i]!
    let hasInf := (g * FastLC.epsilon).terms.size > 0
    if hasInf then
      IO.println s!"  dw2[{i}] = {g} (INFINITE - at decision boundary!)"
    else
      IO.println s!"  dw2[{i}] = {FastLC.std g}"

  IO.println ""
  IO.println "Interpretation:"
  IO.println "  Infinite gradients occur when pre-activation ≈ 0"
  IO.println "  These are the weights that MATTER for the decision!"
  IO.println "  Standard (zero) gradients are in flat regions - no learning signal."
  IO.println ""
  IO.println "  Levi-Civita tells us exactly which weights are at decision boundaries"
  IO.println "  and gives us the direction to push them."

end LeviCivita.BinaryNN
