-- Prove2me | solution 1 for Mpfx.FiniteFormat.subset_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:50:52.273362+00:00
-- url     : https://prove2.me/submissions/e07ba6e7-e4a2-442e-ad90-d84d2ebee02e

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Format_subset_of_mem
import Theorems.Thm_Mpfx_mem_unbounded_of_mem


set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) : F.toFormat ⊆ F.unbounded.toFormat :=
  Format.subset_of_mem subset_rfl fun _ => mem_unbounded_of_mem
end Mpfx.FiniteFormat
