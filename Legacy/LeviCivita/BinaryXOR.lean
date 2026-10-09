import LeviCivita.Fast

-- Binary XOR Network with Levi-Civita Gradients
--
-- XOR is the classic "hard" problem for neural networks.
-- We solve it with a binary network (hard sign activations)
-- and use Levi-Civita to get gradients through the discrete ops.

set_option linter.missingDocs false

namespace LeviCivita.BinaryXOR

open LeviCivita.Fast

def N : FastLC.LC := FastLC.H

-- Hard sign: -1 if x < 0, +1 if x > 0, with infinite derivative at 0
def hardSign (x : Float) : FastLC.LC :=
  if x > 0.01 then FastLC.ofFloat 1.0
  else if x < -0.01 then FastLC.ofFloat (-1.0)
  else N * FastLC.ofFloat x  -- Linear with slope N near 0

def hardSignDeriv (x : Float) : FastLC.LC :=
  if x.abs > 0.01 then FastLC.ofFloat 0.0
  else N  -- Infinite at boundary

-- XOR truth table: inputs in {-1, +1}, output in {-1, +1}
-- (-1,-1) -> -1,  (-1,+1) -> +1,  (+1,-1) -> +1,  (+1,+1) -> -1
def xorData : Array (Float × Float × Float) := #[
  (-1.0, -1.0, -1.0),
  (-1.0,  1.0,  1.0),
  ( 1.0, -1.0,  1.0),
  ( 1.0,  1.0, -1.0)
]

-- Simple 2-2-1 network for XOR
structure XORNet where
  -- Hidden layer: 2 neurons, each with 2 weights + bias
  w1 : Float  -- hidden[0] weight for x1
  w2 : Float  -- hidden[0] weight for x2
  b1 : Float  -- hidden[0] bias
  w3 : Float  -- hidden[1] weight for x1
  w4 : Float  -- hidden[1] weight for x2
  b2 : Float  -- hidden[1] bias
  -- Output layer: 1 neuron with 2 weights + bias
  v1 : Float  -- output weight for hidden[0]
  v2 : Float  -- output weight for hidden[1]
  c  : Float  -- output bias

-- Forward pass returning pre-activations for gradient computation
def XORNet.forward (net : XORNet) (x1 x2 : Float) :
    Float × Float × FastLC.LC × FastLC.LC × Float × FastLC.LC := Id.run do
  -- Hidden layer
  let h1_pre := net.w1 * x1 + net.w2 * x2 + net.b1
  let h2_pre := net.w3 * x1 + net.w4 * x2 + net.b2
  let h1 := hardSign h1_pre
  let h2 := hardSign h2_pre

  -- Output layer
  let y_pre := net.v1 * FastLC.std h1 + net.v2 * FastLC.std h2 + net.c
  let y := hardSign y_pre

  (h1_pre, h2_pre, h1, h2, y_pre, y)

-- Compute output only
def XORNet.predict (net : XORNet) (x1 x2 : Float) : Float :=
  let (_, _, _, _, _, y) := net.forward x1 x2
  FastLC.std y

-- Loss: (y - target)^2 / 4  (normalized since values are in [-1,1])
def loss (y : FastLC.LC) (target : Float) : FastLC.LC :=
  let diff := y - FastLC.ofFloat target
  diff * diff * FastLC.ofFloat 0.25

-- Gradients for all parameters
structure XORGrads where
  dw1 : FastLC.LC
  dw2 : FastLC.LC
  db1 : FastLC.LC
  dw3 : FastLC.LC
  dw4 : FastLC.LC
  db2 : FastLC.LC
  dv1 : FastLC.LC
  dv2 : FastLC.LC
  dc  : FastLC.LC

-- Backward pass with Levi-Civita gradients
def XORNet.backward (net : XORNet) (x1 x2 target : Float) : XORGrads := Id.run do
  let (h1_pre, h2_pre, h1, h2, y_pre, y) := net.forward x1 x2

  -- dL/dy = 2 * (y - target) * 0.25 = 0.5 * (y - target)
  let dL_dy := FastLC.ofFloat 0.5 * (y - FastLC.ofFloat target)

  -- dL/dy_pre = dL/dy * dy/dy_pre
  let dy_pre := hardSignDeriv y_pre
  let dL_dy_pre := dL_dy * dy_pre

  -- Output layer gradients
  let dv1 := dL_dy_pre * h1
  let dv2 := dL_dy_pre * h2
  let dc := dL_dy_pre

  -- Backprop to hidden layer
  let dL_dh1 := dL_dy_pre * FastLC.ofFloat net.v1
  let dL_dh2 := dL_dy_pre * FastLC.ofFloat net.v2

  -- Through hidden activations
  let dh1_pre := hardSignDeriv h1_pre
  let dh2_pre := hardSignDeriv h2_pre
  let dL_dh1_pre := dL_dh1 * dh1_pre
  let dL_dh2_pre := dL_dh2 * dh2_pre

  -- Hidden layer gradients
  let dw1 := dL_dh1_pre * FastLC.ofFloat x1
  let dw2 := dL_dh1_pre * FastLC.ofFloat x2
  let db1 := dL_dh1_pre
  let dw3 := dL_dh2_pre * FastLC.ofFloat x1
  let dw4 := dL_dh2_pre * FastLC.ofFloat x2
  let db2 := dL_dh2_pre

  { dw1, dw2, db1, dw3, dw4, db2, dv1, dv2, dc }

-- Extract finite gradient from LC (scale infinite parts)
def extractGrad (g : FastLC.LC) (scale : Float := 0.01) : Float :=
  -- Check for H (infinite) component by multiplying by ε
  let scaled := g * FastLC.epsilon
  let finiteFromInf := FastLC.std scaled
  if finiteFromInf.abs > 0.0001 then
    finiteFromInf * scale  -- Scale down infinite gradient
  else
    FastLC.std g  -- Use standard part directly

-- Update network
def XORNet.update (net : XORNet) (grads : XORGrads) (lr : Float) : XORNet := {
  w1 := net.w1 - lr * extractGrad grads.dw1
  w2 := net.w2 - lr * extractGrad grads.dw2
  b1 := net.b1 - lr * extractGrad grads.db1
  w3 := net.w3 - lr * extractGrad grads.dw3
  w4 := net.w4 - lr * extractGrad grads.dw4
  b2 := net.b2 - lr * extractGrad grads.db2
  v1 := net.v1 - lr * extractGrad grads.dv1
  v2 := net.v2 - lr * extractGrad grads.dv2
  c  := net.c  - lr * extractGrad grads.dc
}

-- Evaluate accuracy
def XORNet.accuracy (net : XORNet) : Float := Id.run do
  let mut correct := 0
  for (x1, x2, target) in xorData do
    let pred := net.predict x1 x2
    if (pred > 0.0) == (target > 0.0) then
      correct := correct + 1
  correct.toFloat / 4.0

-- Count parameters at decision boundary
def XORNet.countBoundary (net : XORNet) : Nat := Id.run do
  let mut count := 0
  for (x1, x2, _) in xorData do
    let (h1_pre, h2_pre, _, _, y_pre, _) := net.forward x1 x2
    if h1_pre.abs < 0.01 then count := count + 1
    if h2_pre.abs < 0.01 then count := count + 1
    if y_pre.abs < 0.01 then count := count + 1
  count

-- Initial network - designed to be near decision boundaries
def XORNet.init : XORNet := {
  -- XOR can be solved with:
  --   h1 = sign(x1 + x2 + 1)  -- fires when sum > -1 (i.e., not both -1)
  --   h2 = sign(x1 + x2 - 1)  -- fires when sum > 1 (i.e., both +1)
  --   y = sign(h1 - h2)       -- XOR = NAND of (both -1) and (both +1)
  -- Start with noisy version
  w1 := 1.0, w2 := 1.0, b1 := 0.9     -- Almost "OR" gate
  w3 := 1.0, w4 := 1.0, b2 := -0.9    -- Almost "AND" gate
  v1 := 1.0, v2 := -1.0, c := 0.0     -- h1 AND NOT h2
}

#eval do
  IO.println "╔═══════════════════════════════════════════════════════════╗"
  IO.println "║   XOR with Binary Network + Levi-Civita Gradients        ║"
  IO.println "╠═══════════════════════════════════════════════════════════╣"
  IO.println "║   Architecture: 2 -> 2 -> 1 (hard sign activations)      ║"
  IO.println "║   All activations are discrete: output ∈ {-1, +1}        ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝"
  IO.println ""

  let mut net := XORNet.init

  IO.println "XOR Truth Table:"
  IO.println "  x1   x2  | target | predicted"
  IO.println "  ---------|--------|----------"
  for (x1, x2, target) in xorData do
    let pred := net.predict x1 x2
    let mark := if (pred > 0) == (target > 0) then "✓" else "✗"
    IO.println s!"  {x1}  {x2} |  {target}   |   {pred} {mark}"

  IO.println ""
  IO.println s!"Initial accuracy: {net.accuracy * 100}%"
  IO.println s!"Neurons at decision boundary: {net.countBoundary}"
  IO.println ""

  -- Analyze gradients before training
  IO.println "═══ Gradient Analysis (before training) ═══"
  for (x1, x2, target) in xorData do
    let grads := net.backward x1 x2 target
    let (h1_pre, h2_pre, _, _, y_pre, _) := net.forward x1 x2

    IO.println s!"Input ({x1}, {x2}), target={target}:"
    IO.println s!"  Pre-activations: h1={h1_pre}, h2={h2_pre}, y={y_pre}"

    -- Check which gradients are infinite
    let dv1_inf := (grads.dv1 * FastLC.epsilon).terms.size > 0
    let dv2_inf := (grads.dv2 * FastLC.epsilon).terms.size > 0

    if dv1_inf || dv2_inf then
      IO.println s!"  *** INFINITE GRADIENTS (at decision boundary) ***"
      IO.println s!"  dv1 = {grads.dv1}"
      IO.println s!"  dv2 = {grads.dv2}"
    else
      IO.println s!"  Gradients: dv1={FastLC.std grads.dv1}, dv2={FastLC.std grads.dv2}"
    IO.println ""

  -- Training
  IO.println "═══ Training ═══"
  let lr := 0.5

  for epoch in [:50] do
    let mut totalLoss : Float := 0.0

    for (x1, x2, target) in xorData do
      let grads := net.backward x1 x2 target
      net := net.update grads lr

      let (_, _, _, _, _, y) := net.forward x1 x2
      totalLoss := totalLoss + FastLC.std (loss y target)

    if epoch % 10 == 0 || epoch == 49 then
      IO.println s!"Epoch {epoch}: loss={totalLoss/4.0}, accuracy={net.accuracy * 100}%, boundary={net.countBoundary}"

  IO.println ""
  IO.println "═══ Final Results ═══"
  IO.println "  x1   x2  | target | predicted"
  IO.println "  ---------|--------|----------"
  for (x1, x2, target) in xorData do
    let pred := net.predict x1 x2
    let mark := if (pred > 0) == (target > 0) then "✓" else "✗"
    IO.println s!"  {x1}  {x2} |  {target}   |   {pred} {mark}"

  IO.println ""
  IO.println s!"Final accuracy: {net.accuracy * 100}%"

  IO.println ""
  IO.println "═══ Key Insight ═══"
  IO.println "The Levi-Civita gradients are INFINITE at decision boundaries."
  IO.println "This tells us: 'an infinitesimal weight change causes finite output change'"
  IO.println "We extract usable gradients by scaling: grad_usable = st(grad_LC * ε) * scale"
  IO.println ""
  IO.println "This gives mathematical foundation to straight-through estimators!"

end LeviCivita.BinaryXOR
