-- Prove2me | Theorems.Thm_mme_more_asymmetry_cofinal_explicit_child_witness
-- name    : mme_more_asymmetry_cofinal_explicit_child_witness
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-21T20:47:26.135776+00:00
-- url     : https://prove2.me/theorems/fd26c1fe-7510-422d-8c75-054270ba9ce8
-- title:
--   More Asymmetry: unbundled cofinal boundary and interior witness
-- statement:
--   Fix $\tau=3952233/5000000. Construct a cofinal family of physical hash data $D_n$ and recursive constituent stages $A_{n,j}$, together with a value $V>2401$ and errors $e_n\to0$. The source powers tend to infinity, and eventually the same family satisfies raw-source compatibility, all stage and repair budgets, and
--
--   $$
--   (V^6)^{D_n.\mathrm{power}}(1-e_n)\le D_n.\mathrm{rate}(3952233/5000000).
--   $$
--
--   For every child cell $k$ of every factor $j$, specify matrix dimensions $a_{j,k},b_{j,k},c_{j,k}$ whose nested products equal the three global dimensions. Each child satisfies one of the two cases in Section 6: either its grades and full integer profiles identify a boundary tensor with the prescribed factorial/power-of-five dimension, or all three grades are positive and the corresponding matrix-multiplication tensor restricts to the literal child tensor.
--
--   This unbundled certificate isolates the substantive finite construction before those data are packaged into recursive child plans.
--
--   **Formalization Note** Boundary children require only scalar grade, profile, and dimension equalities; actual extraction maps are required only for interior children.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6, Remark 6.1, Theorem 6.2, Sections 6.1-6.6, and Section 7.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_boundary_child_plan
import Mathlib.Topology.Instances.Real.Lemmas

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

theorem mme_more_asymmetry_cofinal_explicit_child_witness {K : Type u} [Field K] :
    ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j))
      (V : ℝ) (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ hraw : MoreAsymmetryRawSourceCompatibility (D n) (A n) K,
          ∃ (a b c : ∀ j, Fin (A n j).childCells → ℕ),
            (∏ j, ∏ k, a j k) = (D n).a ∧
            (∏ j, ∏ k, b j k) = (D n).b ∧
            (∏ j, ∏ k, c j k) = (D n).c ∧
            (∀ j k,
              (A n j).BoundaryChild k (a j k) (b j k) (c j k) ∨
              ((∀ i, 0 < (((A n j).childCell k).2.val i).val) ∧
                TensorObj.Restrict
                  (MMObj K (a j k) (b j k) (c j k))
                  ((A n j).childTensor K k))) ∧
            (∀ j, ((8 ^ (A n j).repairExponent : ℕ) : ℝ) ≤ ((D n).hash j).lower) ∧
            (∏ j, 2 * 8 ^ (A n j).repairExponent) ≤ (D n).repairCopies ∧
            (∀ j, (A n j).Budget) ∧
            (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
              (D n).rate ((3952233 : ℝ) / 5000000) := by sorry
