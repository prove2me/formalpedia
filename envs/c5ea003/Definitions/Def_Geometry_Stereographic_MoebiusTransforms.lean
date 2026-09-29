-- Prove2me | Definitions.Def_Geometry_Stereographic_MoebiusTransforms
-- name    : Geometry_Stereographic_MoebiusTransforms
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:12.70468+00:00
-- url     : https://prove2.me/theorems/1c7f9cc3-5be9-49be-8df9-93d5a686bd5a
-- title:
--   Aether Catalog definitions — Geometry_Stereographic_MoebiusTransforms
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Stereographic.MoebiusTransforms`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Stereographic/MoebiusTransforms.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Geometry.Stereographic.MoebiusTransforms

Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 14
-/


noncomputable section

/-- [Section: # CatalogBuild.Geometry.Stereographic.MoebiusTransforms
Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 14] -/
structure MoebiusParams where
  a : ℝ × ℝ
  b : ℝ × ℝ
  c : ℝ × ℝ
  d : ℝ × ℝ




/-- [Section: # CatalogBuild.Geometry.Stereographic.MoebiusTransforms
Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 14] -/
def moebiusDet (p : MoebiusParams) : ℝ × ℝ :=
  (p.a.1 * p.d.1 - p.a.2 * p.d.2 - (p.b.1 * p.c.1 - p.b.2 * p.c.2),
   p.a.1 * p.d.2 + p.a.2 * p.d.1 - (p.b.1 * p.c.2 + p.b.2 * p.c.1))




def moebiusDetSqNorm (p : MoebiusParams) : ℝ :=
  (moebiusDet p).1 ^ 2 + (moebiusDet p).2 ^ 2








def composeMoebius (p q : MoebiusParams) : MoebiusParams where
  a := (p.a.1 * q.a.1 - p.a.2 * q.a.2 + p.b.1 * q.c.1 - p.b.2 * q.c.2,
        p.a.1 * q.a.2 + p.a.2 * q.a.1 + p.b.1 * q.c.2 + p.b.2 * q.c.1)
  b := (p.a.1 * q.b.1 - p.a.2 * q.b.2 + p.b.1 * q.d.1 - p.b.2 * q.d.2,
        p.a.1 * q.b.2 + p.a.2 * q.b.1 + p.b.1 * q.d.2 + p.b.2 * q.d.1)
  c := (p.c.1 * q.a.1 - p.c.2 * q.a.2 + p.d.1 * q.c.1 - p.d.2 * q.c.2,
        p.c.1 * q.a.2 + p.c.2 * q.a.1 + p.d.1 * q.c.2 + p.d.2 * q.c.1)
  d := (p.c.1 * q.b.1 - p.c.2 * q.b.2 + p.d.1 * q.d.1 - p.d.2 * q.d.2,
        p.c.1 * q.b.2 + p.c.2 * q.b.1 + p.d.1 * q.d.2 + p.d.2 * q.d.1)








def idMoebius : MoebiusParams where
  a := (1, 0)
  b := (0, 0)
  c := (0, 0)
  d := (1, 0)








def moebiusConfFactor (p : MoebiusParams) (z : ℝ × ℝ) : ℝ :=
  let den := (p.c.1 * z.1 - p.c.2 * z.2 + p.d.1,
              p.c.1 * z.2 + p.c.2 * z.1 + p.d.2)
  let den_sq := den.1 ^ 2 + den.2 ^ 2
  Real.sqrt (moebiusDetSqNorm p) / den_sq
























end


