-- Prove2me | solution 1 for Cryptography.IsogenyFoundations.FreeTrans.connector_spec
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:35:09.868639+00:00
-- url     : https://prove2.me/submissions/180555a7-7cdb-4225-9271-9a9be78c4290

import Mathlib
import Definitions.Def_Cryptography_AbstractAlgebra_IsogenyFoundations
open Cryptography.IsogenyFoundations in
theorem solution {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq G] [DecidableEq X]
    (T : FreeTrans G X) (x y : X) : T.act (T.connector x y) x = y := by
  -- the connector is chosen from transitivity
  exact (T.transitive x y).choose_spec
