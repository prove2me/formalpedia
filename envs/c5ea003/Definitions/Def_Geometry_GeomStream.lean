-- Prove2me | Definitions.Def_Geometry_GeomStream
-- name    : Geometry_GeomStream
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:17:02.075919+00:00
-- url     : https://prove2.me/theorems/1cc540d5-84bd-46ae-a737-26176be80e9e
-- title:
--   Aether Catalog definitions — Geometry_GeomStream
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.GeomStream`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/GeomStream.lean by skeleton subtraction
import Mathlib
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Stream.Init
/-
  Coinductive Geometric Streams
  =============================

  A *geometric stream* is the infinite sequence

      a, a*r, a*r^2, a*r^3, ...

  realized as a coinductive object of type `Stream' α`.  Geometric streams are a
  clean formal model of *exact self-similarity*: scaling the whole stream by the
  common ratio `r` produces exactly the tail of the stream.  In other words, the
  stream "looks the same" after one shift, up to multiplication by `r`.

  We build `geomStream` from `Stream'.iterate`, the standard Mathlib coinductive
  iteration combinator, which gives convenient definitional equations for `head`
  and `tail`.  Rather than developing a bespoke bisimulation framework, all
  stream equalities are proved by extensionality on `get n` (`Stream'.ext`),
  which is the directly usable Mathlib idiom.

  Algebraic assumptions are minimized theorem-by-theorem:

  * the closed form and the self-similarity result only need `[Monoid α]`;
  * the stronger "scaling commutes with the generator" compatibility
    (`map_geomStream`) needs `[CommMonoid α]`.
-/

open Stream'

namespace Geometry

variable {α : Type*}

/-- The geometric stream `a, a*r, a*r^2, ...` with first term `a` and common
ratio `r`.  It is defined coinductively by iterating multiplication by `r`. -/
def geomStream [Mul α] (a r : α) : Stream' α :=
  Stream'.iterate (fun x => x * r) a

/-! ### Basic equations -/




/-! ### Closed form -/


/-! ### Shift / tail / drop structure -/




/-! ### Exact self-similarity -/


/-! ### Scaling compatibility -/


end Geometry


