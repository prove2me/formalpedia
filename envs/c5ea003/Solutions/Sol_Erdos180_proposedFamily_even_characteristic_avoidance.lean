-- Prove2me | solution 1 for Erdos180.proposedFamily_even_characteristic_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:22:14.940422+00:00
-- url     : https://prove2.me/submissions/5ac0799f-4978-462b-8e9a-51ca9d0f6db0

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.FieldTheory.Finite.GaloisField
import Theorems.Thm_Erdos180_symplecticQuadrangle_no_encoded_jQuotient_of_char_two

open Erdos180
open SimpleGraph

theorem solution :
    ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)) :=
  fun _ hf j _ =>
    symplecticQuadrangle_no_encoded_jQuotient_of_char_two
      (GaloisField 2 j) hf
