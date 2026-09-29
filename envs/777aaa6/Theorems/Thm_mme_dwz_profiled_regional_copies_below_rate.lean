-- Prove2me | Theorems.Thm_mme_dwz_profiled_regional_copies_below_rate
-- name    : mme_dwz_profiled_regional_copies_below_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T09:03:11.176985+00:00
-- url     : https://prove2.me/theorems/4a233ad6-b275-43fd-8c98-b61749262ff2
-- title:
--   More-Asymmetry regional copies grow at the regional entropy rate
-- statement:
--   Fix a More-Asymmetry regional recipe for fourth-power constituents ($\ell = 2$, half $= 4$):
--   - $R \ge 1$ regions with parent grades $P_r$ (total $8$) and $n_r \ge 1$ positions each;
--   - integer joint counts $m_r(c)$ over admissible left square-child grades, summing to $n_r$;
--   - per-mode complete-split profiles $\mu_i$ with the usual mass, support and boundary consistency;
--   - for each region, a retained mode $\iota_r$ and a prescribed Z-profile $p_r$ with scale $s_r$ that the counts realize, $\sum_{c:\,c_{\iota_r}=j} m_r(c) = p_r(j)\,s_r$.
--
--   Let $E$ be the regional entropy rate of this data (`regionalRate`: the minimum of the X, Y and Z whole-region entropy sums).
--
--   **Statement.** For every $\rho$ with $0 \le \rho < E$, the following holds for all sufficiently large $t$. Scale every count by $t$ and lay the positions out canonically (`positionsAt`). Then there are a target address $a$ for the scaled counts and a number $k \ge e^{\rho t}$ such that the all-mode projection of $CW_5^{\otimes 4\sum_r t n_r}$ onto the inherited DWZ constraints `dwzKeep` is a restriction of $k$ independent copies of one output projection. That projection keeps the words graded at $a$ and useful for the scaled profiles $t\mu$:
--
--   $$\bigoplus_{k}\ \mathrm{tensor}\big(\mathrm{Graded}_a \wedge \mathrm{Useful}_{a,\,t\mu}\big)\ \trianglelefteq\ \mathrm{tensor}\big(\mathrm{dwzKeep}\big),\qquad k \ge e^{\rho t}.$$
--
--   This is the per-region copy count of More Asymmetry §6.6 (arXiv 2404.16349), $2^{\min\{\cdots\} - o(n)}$ copies, with every $o(n)$ term made explicit. It is the rate lemma of the More-Asymmetry regional route to the DWZ fourth-power bound.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Mathlib
import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_dwz_profiled_regional_keep_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data

open BigOperators Filter MME MME.TensorObj MME.RecursiveYZ MME.RegionRate MME.RegionRealization
  MME.DWZProfiledRegional MME.CompleteSplit MME.DWZRestrictedValue MME.RecursiveYZ.CWCells
open scoped Classical

universe u

set_option autoImplicit false

theorem mme_dwz_profiled_regional_copies_below_rate {K : Type u} [Field K] {R : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * 4)
    (n : Fin R → ℕ) (hn : ∀ r, 0 < n r) (hR : 0 < R)
    (m : ∀ r, RecursiveThinSplit.Split 4 (parent r) → ℕ) (hm : ∀ r, ∑ c, m r c = n r)
    (mu : Fin 3 → Cell 4 R parent → CompleteSplit.CompleteWord 2 → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (hsupport : ∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val)
    (hboundary : BoundaryProfiles mu)
    (keptMode : Fin R → Fin 3) (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (hprofile : ∀ r j,
      (∑ c : {c : RecursiveThinSplit.Split 4 (parent r) // c.val (keptMode r) = j},
        m r c.val) = (p r).count j * scale r)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < regionalRate htotal n m mu) :
    ∀ᶠ t : ℕ in atTop, ∃ k : ℕ, Real.exp (ρ * t) ≤ k ∧
      ∃ a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin k ↦ ProfiledCW.tensor K (fun i x ↦
            Graded htotal i a (ProfiledCW.split (positionsAt n t) (lengthAt n t) x) ∧
              Useful (fullCell htotal a) (fun c w ↦ t * mu i c w)
                (ProfiledCW.split (positionsAt n t) (lengthAt n t) x))))
          (ProfiledCW.tensor K (dwzKeep parent (fun r ↦ t * n r) keptMode p
            (fun r ↦ t * scale r) (positionsAt n t) (lengthAt n t))) := by sorry
