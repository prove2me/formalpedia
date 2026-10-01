-- Prove2me | Theorems.Thm_mme_released_interior_scaled_parent_graded_fine_word_window
-- name    : mme_released_interior_scaled_parent_graded_fine_word_window
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T00:01:03.633933+00:00
-- url     : https://prove2.me/theorems/464f6f2b-efd1-48d0-9e63-96ffb0545e1e
-- title:
--   Parent-graded source inclusion for all released interior cells
-- statement:
--   Fix one of the six released owners $o$, an interior cell $s$, and a positive integer scale $k$. Write $D=10^{12}$ and $T=kD^4$. There is a single bijection from the $2T$ child positions to the child positions of the six regions with sizes prescribed by the released data. This bijection works simultaneously for every mode $i$, every fine word $x\in\{0,1,2\}^{4T}$, and every real tolerance $\varepsilon$.
--
--   Suppose that, in each regional parent occurrence, the grades of its two child words add up to the prescribed parent grade $g_{s,i}$. Suppose also that each regional empirical distribution of ordered pairs of child words differs from its prescribed parent mixture by less than $\varepsilon$ in every entry. Let $X_p\in\{0,1,2\}^4$ be the $p$-th consecutive four-letter block of the original word $x$. Then
--
--   $$
--   \sum_{q=0}^{3} X_p(q)=g_{s,i}\quad\text{for every }p,
--   \qquad
--   \left|\frac{\#\{p:X_p=w\}}{T}-\frac{C_{o,s,i}(w)}{D^4}\right|\leq\varepsilon\quad\text{for every }w\in\{0,1,2\}^4,
--   $$
--
--   where $C_{o,s,i}(w)$ is the total integer weight of released joint rows whose mode-$i$ word is $w$. Regions of size zero are allowed; their empirical frequencies and prescribed mixtures are taken to be zero. The grade hypothesis constrains the sum of the two child grades, without prescribing either child's grade separately.
--
--   This supplies source-window inclusion at the released profile center for the parent-graded recursive interface. It does not assert the existence of a typical word or construct the full recursive tensor recipe.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu and Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/pdf/2404.16349v2, Section 6.1 and Claim 6.5, printed p. 32. This is an interface lemma for the platform's released integer profiles, not a verbatim statement from the paper. It extends Robertboy18's accepted general child-graded inclusion (theorem 47e4a0f7-cf71-400b-8090-52f1cb4ce238, solution 65026bdb-3b76-49c8-9e04-fb69fbab0a3f) to the parent-graded hypothesis already used in the accepted 116-cell case (theorem a5e7b142-f07d-4880-9db6-6fcbe1c76ecc, solution b4597884-9ad3-499a-bcd1-90324d3a723d).

import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_released_interior_scaled_partition_parent_window
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_complete_split_concatenation
import Definitions.Def_mme_released_interior_integer_profiles
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization
open scoped Classical
set_option autoImplicit false

theorem mme_released_interior_scaled_parent_graded_fine_word_window
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (k : ℕ) (hk : 0 < k) :
    ∃ childPositions : Fin ((k * denominator ^ 4) * 2) ≃
        Position (fun r : Fin 6 => k * (regionalSize owner s) r),
      ∀ (i : Fin 3)
        (x : ProfiledCW.FineWord ((k * denominator ^ 4) * 4)) (eps : ℝ),
        ParentGraded (parent s) (fun r => k * (regionalSize owner s) r) i (ProfiledCW.split childPositions
          (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
            (k * denominator ^ 4) * 4 from Nat.mul_assoc (k * denominator ^ 4) 2 2) x) →
        parentTypical (parent_total s) (fun r => k * (regionalSize owner s) r)
          (fun r c => k * (splitCount owner s) r c) (fun c w => k * (integerProfile owner s) i c w) eps
          (ProfiledCW.split childPositions
            (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
              (k * denominator ^ 4) * 4 from Nat.mul_assoc (k * denominator ^ 4) 2 2) x) →
        (∀ p : Fin (k * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p q).val)
            = (parent s) 0 i) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows owner s).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by sorry
