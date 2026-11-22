-- Prove2me | Definitions.Def_BruhatTits
-- name    : BruhatTits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:28:07.233007+00:00
-- url     : https://prove2.me/theorems/e6fd3044-f8e5-4e0c-b098-029ac45ef1eb
-- title:
--   Bruhat Tits
-- statement:
--   Definitions and structural lemmas for Bruhat Tits, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits.lean

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Graph_Edges
import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Orientation
import Definitions.Def_BruhatTits_Graph_Regular
import Definitions.Def_BruhatTits_Graph_Tree
import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Harmonic_Application
import Definitions.Def_BruhatTits_Harmonic_Basic
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Utils_IsBasisOn
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_Order
import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false


