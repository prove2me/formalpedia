-- Prove2me | Theorems.Thm_mme_recursive_region_exact_step_realization_of_graded_source
-- name    : mme_recursive_region_exact_step_realization_of_graded_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T01:59:12.880414+00:00
-- url     : https://prove2.me/theorems/ba4853ad-7d15-4522-be6a-cdc0e3d92cc5
-- title:
--   ExactStep realization for any source predicate containing the unbroken target words
-- statement:
--   Fix a finite family of $R$ recursive regions with parent types $\mathrm{parent}(r) \in \{0,\dots\}^3$ satisfying $\sum_i \mathrm{parent}(r)_i = 2\,\mathrm{half}$, integer cell multiplicities $m$, and per-mode cell word profiles $\mu_i$ with the mass, support and boundary consistency of the recursive Y/Z construction. Let $P$ be **any** predicate on flat CW words of length $M$ such that every unbroken word at every target address satisfies it:
--
--   $$\forall i,\ \forall a \in \mathrm{target}(m),\ \forall f \in \mathrm{unbrokenWords}(i,a,\mu_i),\qquad P\big(i,\ \mathrm{flatten}(f)\big).$$
--
--   Assume the usual finite realization inputs: a reference address in the target, a divisor $k$ of every multiplicity with $k \le n_r$, a repair base $d > 1$, a tolerance $\varepsilon > 0$, and the polynomial size condition
--
--   $$8d \cdot 25R\,\big|\mathrm{CompleteWord}(\ell)\big|^2 \;\le\; k\,\varepsilon^2 .$$
--
--   Then there exists an exact step $E$ for the source predicate $P$ whose selected count satisfies
--
--   $$\frac{|\mathrm{target}(m)|\; e^{-4\sqrt{\log Q}}}{32\,Q} \;\le\; E.\mathrm{count},$$
--
--   where $Q$ is the common hash scale of the Y/Z loads, whose repair exponent is exactly $\lfloor \log_d \mathrm{cap}\rfloor + 1$ for the block capacity $\mathrm{cap}$, and whose output is the graded-and-useful predicate at the reference address.
--
--   This is the companion of `mme_recursive_region_actual_exact_step_realization`, which fixes $P$ to the parent-typical band and pays for it with the derived hole budget. It is *not* a strengthening of that statement: the parent-typical band does not satisfy the hypothesis above. It is the complementary case in which the source predicate holds identically on unbroken target words, so the X-mode hole set is empty; the Y and Z hole budgets are unchanged and still come from the hash selection. The intended instance is a predicate expressing inherited parent-profile constraints, for which the containment hypothesis is an accepted theorem.
--
--   No asymptotic statement, tensor restriction, or numerical exponent bound is asserted; this is a finite realization record.
-- source:
--   Quantitative finite realization for a jointly processed constituent region with an arbitrary source predicate, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . Companion of mme_recursive_region_actual_exact_step_realization (same construction, source predicate abstracted). This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Mathlib
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_region_hash_loads

open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem mme_recursive_region_exact_step_realization_of_graded_source {half R ell N L M : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (ell - 1) = M)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (hsupport : ∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val)
    (hboundary : BoundaryProfiles mu)
    (reference : Address half R parent n) (href : reference ∈ RecursiveXHash.target m)
    (k d : ℕ) (hk : 0 < k) (hd : 1 < d) (hkn : ∀ r, k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) ≤
      (k : ℝ) * eps ^ 2)
    (P : Predicate M)
    (hP : ∀ (i : Fin 3) (a : Address half R parent n), a ∈ RecursiveXHash.target m →
      ∀ f ∈ unbrokenWords htotal i a (mu i), P i (ProfiledCW.flatten positions length f)) :
    let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
    let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
    let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
    ∃ E : ExactStep ell M P,
      ((RecursiveXHash.target (n := n) m).card : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
      E.stage.repairExponent = Nat.log d cap + 1 ∧
      E.output = fun i x ↦ Graded htotal i reference (ProfiledCW.split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (ProfiledCW.split positions length x) := by sorry
