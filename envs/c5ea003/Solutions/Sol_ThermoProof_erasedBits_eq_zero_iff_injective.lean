-- Prove2me | solution 1 for ThermoProof.erasedBits_eq_zero_iff_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:10:01.527356+00:00
-- url     : https://prove2.me/submissions/65e77e7d-03a6-45a3-8778-cfc80cfc29c1

-- Sol generated from Novelty/ThermodynamicsOfProof.lean
import Mathlib
import Definitions.Def_Novelty_ThermodynamicsOfProof
import Theorems.Thm_ThermoProof_imageCard_pos

/-!
# Thermodynamics of Mathematical Proof

A **Landauer-like principle for mathematical reasoning**.

We model a single *proof step* (a rewrite, a case merge, a lookup, a verification) as a
function `f : α → β` between finite state spaces.  Physically, a computation that is
*logically irreversible* — one that maps several distinct inputs to the same output —
must dump the lost distinctions into the environment.  Landauer's principle states that
erasing one bit of information costs at least `k_B · T · ln 2` of dissipated entropy.

The information erased by the step `f` is the drop in Shannon capacity of the register:

  `erasedBits f = log₂ (card α) − log₂ (image size of f)`.

## Main results

* `erasedBits_nonneg` — a proof step never *un*-erases information.
* `erasedBits_eq_zero_iff_injective` — **reversibility criterion**: a step erases zero bits
  iff it is injective (logically reversible).
* `landauerCost_pos_of_not_injective` — **Landauer's principle**: an irreversible step costs
  strictly positive entropy at positive temperature.
* `erasedBits_lower_bound` — the erasure of any step into a `card β`-state register is at
  least `log₂(card α) − log₂(card β)`.
* `erasedBits_mono_comp` — **erasure is monotone along a proof pipeline**: composing steps
  can only accumulate erasure, never undo it (a data-processing inequality).
* `erasedBits_bennett` — **Bennett's reversible embedding**: *retaining the input* makes any
  step reversible (erases zero bits), so erasure is not forced by computation per se.
* `erasedBits_collapse` / `erasedBits_bigCollapse` — explicit families realising *linear*
  and *exponential* erasure in a size parameter.
* `exponential_erasure_separation` — there are theorems (state collapses) whose verification
  erases unboundedly (indeed exponentially) many bits.
* `incompressible` — a Kolmogorov counting bound: the `2ⁿ` Boolean predicates on `n` bits
  cannot be injectively coded by the `2ⁿ − 1` programs of length `< n`, so some predicate has
  no proof/description shorter than `n` bits — its verification erases `≥ n · k_B T ln 2`.
-/

open Finset Real

open ThermoProof

/-! ## Information erased by a proof step -/





lemma imageCard_of_injective {α β : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) : imageCard f = Fintype.card α := by
  unfold imageCard; rw [Finset.card_image_of_injective _ hf]; simp [Finset.card_univ]




/-! ## The Landauer cost -/





/-! ## Erasure accumulates along a proof (data-processing) -/



/-! ## Bennett's reversible embedding: erasure is avoidable -/




/-! ## Explicit erasure families and the exponential separation -/











/-! ## Kolmogorov incompressibility and the cost of verification -/



open ThermoProof in
theorem solution{α β : Type*} [Fintype α] [DecidableEq β] [Nonempty α]
    (f : α → β) : erasedBits f = 0 ↔ Function.Injective f := by
  unfold erasedBits
  have h1 : (0:ℝ) < imageCard f := by exact_mod_cast imageCard_pos f
  have hα : (0:ℝ) < Fintype.card α := by
    have : 0 < Fintype.card α := Fintype.card_pos; exact_mod_cast this
  constructor
  · intro h
    have hlog : Real.logb 2 (Fintype.card α) = Real.logb 2 (imageCard f) := by linarith
    have hcard : (Fintype.card α : ℝ) = imageCard f :=
      Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr hα) (Set.mem_Ioi.mpr h1) hlog
    have hcard' : Fintype.card α = imageCard f := by exact_mod_cast hcard
    have hcard'' : imageCard f = (Finset.univ : Finset α).card := by
      unfold imageCard at hcard' ⊢; simp [Finset.card_univ] at hcard' ⊢; omega
    have hinj := Finset.injOn_of_card_image_eq hcard''
    intro a b hab; exact hinj (by simp) (by simp) hab
  · intro hinj
    rw [imageCard_of_injective hinj]; ring
