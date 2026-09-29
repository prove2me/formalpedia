-- Prove2me | Theorems.Thm_mme_Ctensor_three_unequal_word_induced_matching_extraction
-- name    : mme_Ctensor_three_unequal_word_induced_matching_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:32:40.247357+00:00
-- url     : https://prove2.me/theorems/fe76e44b-437d-45ef-9340-a26122a99793
-- title:
--   Unequal-alphabet word matchings yield literal three-star matrix-multiplication extractions
-- statement:
--   Let $X,Y,Z$ have actual C-tensor certificates of shapes $\langle1,H_0,1\rangle$, $\langle1,H_1,1\rangle$, and $\langle1,H_2,1\rangle$, with component matrix-multiplication volumes $v_0,v_1,v_2$.
--
--   Choose three injective lists of words of a common length $R$ over the respective alphabets, with list sizes $W_0,W_1,W_2$. Let $E\subseteq[W_0]\times[W_1]\times[W_2]$ be an actual induced matching: its three pair-coordinate projections are injective, and any three edges with the cyclic overlap equalities must be the same edge.
--
--   Then there are matrix-multiplication dimensions $a_e,b_e,c_e$, indexed by exactly $|E|$ elements, such that
--   $
--   \bigoplus_{e\in E}\langle a_e,b_e,c_e\rangle
--   \le_{\mathrm{restriction}}
--   \bigl(X\otimes\operatorname{cyc}(Y)\otimes\operatorname{cyc}^2(Z)\bigr)^{\otimes R},
--   \qquad
--   a_eb_ec_e=(v_0v_1v_2)^R.
--   $
--   The extracted dimensions may differ between summands, while their volumes agree. Alphabets, list sizes, component volumes, and word frequencies need not agree. No cardinality lower bound or scalar tensor-value assertion is assumed or supplied.
-- source:
--   Derived finite unequal-alphabet generalization of the existing source-faithful cyclic C-tensor grading/extraction proofs: Prove2Me mme_Ctensor_three_cyclic_balanced_grading_certificate, Proved777 theorem70dd3098-5d4f-4668-88bf-a3ddbd48c6a1, accepted submission22a6a66a-36b3-4edd-8bca-6c73f3f4f948; and mme_Ctensor_three_balanced_cyclic_induced_matching_extraction, Proved777 theorem92df093a-e7af-4448-b1b5-497ac31a6896, accepted submissionbfc16e75-97d5-4b7d-b234-96fba533ad3c. The coordinate construction and induced graded-address zeroing implement the cyclic laser extraction underlying Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation9(1990), journal pp271–272, https://doi.org/10.1016/S0747-7171(08)80013-2. This is an explicitly derived finite interface, not claimed as a separately numbered paper theorem. Its arbitrary word lists deliberately remove balanced-frequency assumptions unused by the finite tensor proof.

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_threeStarCyclicProduct

open MME

universe u

set_option autoImplicit false

theorem mme_Ctensor_three_unequal_word_induced_matching_extraction
    {K : Type u} [Field K] {X Y Z : TensorObj K 3}
    {H0 H1 H2 v0 v1 v2 R W0 W1 W2 : ℕ}
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (w0 : Fin W0 → Fin R → Fin H0) (hw0 : Function.Injective w0)
    (w1 : Fin W1 → Fin R → Fin H1) (hw1 : Function.Injective w1)
    (w2 : Fin W2 → Fin R → Fin H2) (hw2 : Function.Injective w2)
    (E : Finset (Fin W0 × Fin W1 × Fin W2))
    (_hxy : Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)))
    (_hyz : Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)))
    (_hzx : Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)))
    (hinduced : ∀ x y z : E,
      x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 → z.1.1 = x.1.1 →
      x = y ∧ y = z) :
    ∃ a b c : Fin E.card → ℕ,
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
        ((threeStarCyclicProduct X Y Z).kronPow R) ∧
      ∀ i, a i * b i * c i = (v0 * v1 * v2) ^ R := by sorry
