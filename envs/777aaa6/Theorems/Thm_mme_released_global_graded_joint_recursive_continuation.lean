-- Prove2me | Theorems.Thm_mme_released_global_graded_joint_recursive_continuation
-- name    : mme_released_global_graded_joint_recursive_continuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T16:38:10.855091+00:00
-- url     : https://prove2.me/theorems/710d14e4-fb59-4441-b935-62646b2dab1d
-- title:
--   Graded recursive continuation of the released global candidate
-- statement:
--   This is the recursive continuation for the published exact global candidate, with **graded-source** constituent steps.
--
--   Set $B=D^5k^2$ and $n=6B$. There are six positive tolerance caps with the following property. For every choice of smaller positive regional tolerances and every lower bound on $k$, some larger integer $k$ works as follows. For every admissible reference arrangement of the six global profiles, their physical joint window admits one graded logarithmic joint recipe $R$ at level three, with input count $U_R\geq1$, positive dimension product $abc$, and
--   $$n\,\frac{13223546}{10000000}+\log U_R\leq L_R,$$
--   $$n\left(3\cdot\frac{209612367517}{100000000000}-10^{-7}\right)\leq\log(abc).$$
--
--   It is the same statement as `mme_released_global_joint_recursive_continuation`, except for the kind of recipe. That version asks for an ordinary `LogJointRecipe`, which the joint window rules out. The window requires every global block to have exactly its reference grade. The first recursive hashing step splits each global block into two halves. Its source must contain the step's whole typical band at tolerance $\varepsilon$, and the size test forces $\varepsilon\geq 1/\sqrt{\text{minimum}}$. That band therefore contains words in which about $\varepsilon n$ blocks have halves whose grades do not add up to the block's grade. Such words are not in the window.
--
--   Graded-source steps (`IntegerStepG`) only need the band's parent-graded words to lie in the source. Parent-graded is exactly the window's grade condition.
--
--   The recursive rate $1.3223546$ plus the proved global rate $2235998128/1500000000$ exceeds $2.81302098456-10^{-6}$. The recursive rate of the released parameters is about $1.3223555$.
-- source:
--   Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349), sections 5-6: recursive regional hashing after the global extraction. Exact asymptotic statement as written.

import Definitions.Def_mme_released_global_joint_interface
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false

theorem mme_released_global_graded_joint_recursive_continuation :
    ∃ eta : Fin 6 → ℝ, (∀ o, 0 < eta o) ∧
      ∀ eps : Fin 6 → ℝ, (∀ o, 0 < eps o) → (∀ o, eps o ≤ eta o) →
        ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
          ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
            ∃ R : LogJointRecipeG (4 * (6 * blocks (k^2))) 3 (jointWindow (k^2) hk a eps),
              1 ≤ R.inputs ∧ 1 ≤ R.a * R.b * R.c ∧
              (6 * blocks (k^2) : ℕ) * ((13223546 : ℝ)/10000000) +
                Real.log (R.inputs : ℝ) ≤ R.logOutputs ∧
              (6 * blocks (k^2) : ℕ) *
                (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
                  Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by sorry
