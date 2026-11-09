-- Prove2me | Theorems.Thm_Couret_S5_full_equals_proper_of_six
-- name    : Couret.S5.full_equals_proper_of_six
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:41:08.333032+00:00
-- url     : https://prove2.me/theorems/d7953c3e-fe93-448b-9ff2-6e781e7eccb3
-- title:
--   Full and proper product supports agree from length six
-- statement:
--   Let $w$ be a finite word in the eight unit residues modulo 30, of length at least six. For each code $u$,
--
--   $$u\text{ is a product of a selection of occurrences}\quad\Longleftrightarrow\quad u\text{ is a product of a nonempty proper selection}. $$
--
--   Selections use labeled occurrences, so factors may repeat. This removes the empty and full selections from the support without changing it.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/DavenportThreshold.lean, lines 62–70; source file SHA-256 c800425f72bd7cac263232227e182bea9d8881d436ee30021d29b43628c45e05; theorem Couret.S5.full_equals_proper_of_six

import Definitions.Def_Couret_DavenportThreshold_ac37b2f8de8c
import Std
import Theorems.Thm_Couret_Choice_eval_mul_complement
import Theorems.Thm_Couret_Choice_omitted_complement
import Theorems.Thm_Couret_Choice_picked_complement
import Theorems.Thm_Couret_S5_rank_facts
import Theorems.Thm_Couret_S5_rank_initial
import Theorems.Thm_Couret_S5_subRun_bound
import Theorems.Thm_Couret_S5_subRun_exact
import Theorems.Thm_Couret_fullSupport_iff
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
namespace Couret
namespace S5

theorem full_equals_proper_of_six (w : Word Code30) (hw : 6 ≤ length w) (u : Code30) :
    fullSupport mod30Product w u ↔ properSupport mod30Product w u := by sorry










end S5
end Couret
