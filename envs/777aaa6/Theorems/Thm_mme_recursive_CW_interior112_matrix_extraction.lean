-- Prove2me | Theorems.Thm_mme_recursive_CW_interior112_matrix_extraction
-- name    : mme_recursive_CW_interior112_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:31:45.953341+00:00
-- url     : https://prove2.me/theorems/a964c3d8-8e98-4f5d-8a10-c282637dbb5b
-- title:
--   Explicit four-count matrix extraction in a (1,1,2) interior block
-- statement:
--   Let $a,b,c,d$ be nonnegative integers and put $L=a+b+c+d$. Write $10,01,02,11,20$ for the corresponding length-two words over $\{0,1,2\}$. Consider the intact complete-word profile block of $\mathrm{CW}_5^{\otimes 2L}$ over a field $K$, with grade $(1,1,2)$ at every child position and histograms
--   $$\begin{aligned}
--   \mu_0(10)&=a+b,&\mu_0(01)&=c+d,\\
--   \mu_1(10)&=a+c,&\mu_1(01)&=b+d,\\
--   \mu_2(02)&=a,&\mu_2(11)&=b+c,&\mu_2(20)&=d.
--   \end{aligned}$$
--   All unspecified histogram entries are zero. Then this literal intact block $T_{112}(a,b,c,d)$ admits the matrix restriction
--   $$\langle5^{b+c},5^{a+d},5^{b+c}\rangle_K\preceq T_{112}(a,b,c,d).$$
--   The parameters are the joint counts of the supported triples $(10,10,02)$, $(10,01,11)$, $(01,10,11)$, and $(01,01,20)$, respectively. The result supplies an explicit family of interior-cell extractions, including zero counts, without requiring tensor maps or joint-histogram witnesses as inputs. It asserts the dimensions obtained from a fixed supported assignment, with no additional multiplicity gain.
-- source:
--   Four supported length-two grade triples and intact-block extraction from their integer joint histogram.

import Theorems.Thm_mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells
open scoped Classical

theorem mme_recursive_CW_interior112_matrix_extraction {K : Type*} [Field K] (a b c d : ℕ) :
    let mu : Fin 3 → CompleteWord 2 → ℕ :=
      ![fun s ↦ (if s = ![1, 0] then a + b else 0) +
          (if s = ![0, 1] then c + d else 0),
        fun s ↦ (if s = ![1, 0] then a + c else 0) +
          (if s = ![0, 1] then b + d else 0),
        fun s ↦ (if s = ![0, 2] then a else 0) +
          (if s = ![1, 1] then b + c else 0) + (if s = ![2, 0] then d else 0)]
    Restrict (MMObj K (5 ^ (b + c)) (5 ^ (a + d)) (5 ^ (b + c)))
      (unbroken K 5 2 (a + b + c + d) (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ ![1, 1, 2]) (fun i _ ↦ mu i)) := by sorry
