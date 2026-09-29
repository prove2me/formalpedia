-- Prove2me | Theorems.Thm_mme_dwz_q5_odd_coarse_prescribed_z_word_card
-- name    : mme_dwz_q5_odd_coarse_prescribed_z_word_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T09:28:38.177437+00:00
-- url     : https://prove2.me/theorems/069b4235-70ac-471f-8436-1321e3074b2d
-- title:
--   Exact prescribed-Z word counts for the q=5 odd coarse grades
-- statement:
--   Let $p=(p_0,p_1,p_2;d)$ be an integer fine-$Z$ profile and let $N=dm$. In the actual canonical $q=5$ coarse-grade-$1$ alphabet, if $p_2=0$, the number of length-$N$ words with exactly $mp_a$ left-grade-$a$ letters is
--   \[\binom{dm}{mp_0,mp_1,mp_2}5^{dm}.\]
--   The same formula holds in coarse grade $3$ if $p_0=0$. Both are proved using explicit grade-preserving bijections with two grade choices and five internal letters.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Definition 3.9 and Section 7.3 after Lemma 7.14. Exact finite type-class count for the elementary boundary prescribed-Z projection; the paper uses its entropy asymptotic.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_prescribed_product_alphabet_word_card
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
open scoped BigOperators
universe u
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem mme_dwz_q5_odd_coarse_prescribed_z_word_card (p : IntegerZSplitProfile 3) (m : ℕ) :
    (p.count 2 = 0 →
      Nat.card {w : PowIndex (LiftedCoarsePair.{u} 5 1) (p.length m) //
        prescribedZWord LiftedCoarsePair.leftGrade p m w} =
        Nat.multinomial Finset.univ (fun a : Fin 3 ↦ p.count a * m) * 5 ^ p.length m) ∧
    (p.count 0 = 0 →
      Nat.card {w : PowIndex (LiftedCoarsePair.{u} 5 3) (p.length m) //
        prescribedZWord LiftedCoarsePair.leftGrade p m w} =
        Nat.multinomial Finset.univ (fun a : Fin 3 ↦ p.count a * m) * 5 ^ p.length m) := by sorry
