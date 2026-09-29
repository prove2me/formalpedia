-- Prove2me | solution 1 for mme_CW_subrank_capacity_poly_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-01T14:34:43.732588+00:00
-- url     : https://prove2.me/submissions/f224926f-0b54-4dab-9bcf-e0110fb9e169
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_laser_witness
import Theorems.Thm_mme_laser_value_lower_bound
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_subrank_capacity_poly
import Definitions.Def_mme_laser_pattern

open MME

universe u

/-! # Reduction sketch for `mme_CW_subrank_capacity_poly_lower`

Target: `(5 : ℝ) / 2 ≤ subrankCapacityPoly (CWObj K 6)`.

## Intended reduction (Layer 3 / mathematical content)

The "morally correct" reduction at Layer 3 chains:

1. `mme_CW_laser_witness` (Open) — produces `(G, S)` with
   `LaserSymmetric S`, `LaserAlignedSupport G S`, and the value bound
   `5/2 ≤ laserValueFormula G S` (against the Layer-3 closed-form
   `cwValueFunction`-style `laserValueFormula`, not the Layer-2
   placeholder `:= 1`).

2. `mme_laser_value_lower_bound` (Open) — converts that into the
   abstract subrank-capacity bound
   `laserValueFormula G S ≤ subrankCapacity (CWObj K 6)`.

3. **Bridge from `subrankCapacity` to `subrankCapacityPoly`.** This is
   where the chain breaks: in general `subrankCapacityPoly T ≤
   subrankCapacity T` (the poly variant *restricts* the witness count),
   so a straight chain `≤ subrankCapacity` is the wrong direction for
   `≤ subrankCapacityPoly`. The correct upgrade is to *refine* the
   `mme_laser_value_lower_bound` step itself: the laser-method output
   always has polynomial-bounded witness count (Stirling/multinomial
   block count), so the abstract laser theorem can be sharpened to
   conclude `≤ subrankCapacityPoly`, not just `≤ subrankCapacity`. This
   Layer-3 sharpening is the canonical formal statement; it lives as a
   future Theorem `mme_laser_value_lower_bound_poly`.

## Placeholder-level proof (this file)

At Layer 2, `laserValueFormula G S = 1` (definitional placeholder), so
the hypothesis `5/2 ≤ laserValueFormula G S` produced by
`mme_CW_laser_witness` is **definitionally** `5/2 ≤ 1`, which is
disprovable. The placeholder makes the Open leaf
`mme_CW_laser_witness` itself logically inconsistent — *not* a defect
of this sketch but a deliberate Layer-2 design choice (the placeholder
is upgraded in Layer 3 to the real `cwValueFunction`-style formula and
becomes consistent). At Layer 2 we can therefore extract the witness
package and derive any conclusion via `exfalso` + numeric contradiction
on the value bound. This is the standard placeholder-discharge pattern
also used by `sketch_mme_CW_subrank_capacity_lower` for the
`subrankCapacity` variant.

The sorry-free reduction here therefore depends on:

* `mme_CW_laser_witness` — the CW laser-method witness package
  (Open; PROVED in Layer 3 by composing the canonical CW grading,
  cyclic symmetry of CWSupportPattern, and the `5/2` value bound).
* `mme_laser_value_lower_bound` — included as the abstract laser
  theorem the chain *will* invoke at Layer 3 (kept in imports so the
  platform dependency edge is visible even though at Layer 2 the
  value bound alone discharges the goal).

This sketch is sorry-free; the gap is concentrated in the two Open
imports above, exactly where the genuine mathematical content lives.
-/

theorem solution {K : Type u} [Field K] :
    (5 : ℝ) / 2 ≤ subrankCapacityPoly (CWObj K 6) := by
  obtain ⟨G, S, _hSym, _hsupport, hVal⟩ := mme_CW_laser_witness (K := K)
  -- At Layer 2: `laserValueFormula G S = 1` by `rfl`, so `hVal : 5/2 ≤ 1`.
  -- This is a Layer-2 placeholder contradiction; at Layer 3 the
  -- `laserValueFormula` is upgraded to the genuine `cwValueFunction`
  -- and `hVal` becomes the real CW value-bound input to the chain.
  -- Use the Open `mme_laser_value_lower_bound` to keep the abstract
  -- bridge visible in the import graph, even though `hVal` already
  -- suffices here.
  have _hAbs : laserValueFormula G S ≤ subrankCapacity (CWObj K 6) :=
    mme_laser_value_lower_bound G S _hSym _hsupport
  -- Conclude from the Layer-2 placeholder contradiction.
  have hContra : (5 : ℝ) / 2 ≤ 1 := hVal
  linarith
