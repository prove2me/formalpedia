-- Prove2me | Definitions.Def_Logic_KneeFluctuationEvidence
-- name    : Logic_KneeFluctuationEvidence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:55:32.170866+00:00
-- url     : https://prove2.me/theorems/b4d9f934-2bff-4801-86c4-d69fdc5e92ca
-- title:
--   Aether Catalog definitions — Logic_KneeFluctuationEvidence
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.KneeFluctuationEvidence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/KneeFluctuationEvidence.lean by skeleton subtraction
import Mathlib
/-
# Computational evidence for the NET-44 knee analysis

Small, fully decidable checks on the measured sweep, carried out in `ℚ` so that the
kernel can evaluate them (`decide` / `norm_num`, never `native_decide`).  They confirm the
arithmetic that the theorems in `Logic.KneeFluctuationTwoSeed` reason about abstractly:

* the seed-1 sweep has knee `128` and the seed-2 sweep has knee `96` at the bar `0.98`;
* the seed-1 margin at `96` (`0.003`) is *smaller* than the observed inter-seed spread
  (`0.010`), while the seed-1 deficit at `64` (`0.012`) is *larger* — exactly the
  asymmetry that makes the upper end of the bracket seed-lucky and the lower end robust;
* shifting the seed-1 sweep by the spread reproduces the seed-2 numbers to within
  `0.001` and moves the knee to `96`.
-/


namespace KneeEvidence

/-- Retained-accuracy bar, as an exact rational. -/
def barQ : ℚ := 98 / 100

/-- Observed inter-seed spread, as an exact rational. -/
def spreadQ : ℚ := 10 / 1000

/-- The measured seed-1 sweep (NET-37) at `(d = 4, ctx = 1024)`, budgets in increasing
order.  Only budgets that were actually swept are listed. -/
def sweepS1 : List (ℕ × ℚ) :=
  [(64, 968 / 1000), (96, 977 / 1000), (128, 986 / 1000)]

/-- The measured seed-2 sweep (NET-44), with the added `112` pinning point. -/
def sweepS2 : List (ℕ × ℚ) :=
  [(64, 979 / 1000), (96, 987 / 1000), (112, 991 / 1000), (128, 993 / 1000)]

/-- The knee of a sweep: the first budget whose retained accuracy reaches the bar. -/
def kneeOf (s : List (ℕ × ℚ)) : Option ℕ := (s.find? fun p => barQ ≤ p.2).map Prod.fst

/-- The sweep shifted uniformly by the observed spread. -/
def shift (s : List (ℕ × ℚ)) (η : ℚ) : List (ℕ × ℚ) := s.map fun p => (p.1, p.2 + η)








end KneeEvidence


