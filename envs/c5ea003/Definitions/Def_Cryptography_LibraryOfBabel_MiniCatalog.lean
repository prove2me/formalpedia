-- Prove2me | Definitions.Def_Cryptography_LibraryOfBabel_MiniCatalog
-- name    : Cryptography_LibraryOfBabel_MiniCatalog
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:19:57.224996+00:00
-- url     : https://prove2.me/theorems/80e0c347-5cd6-4014-af65-37f93b6024d4
-- title:
--   Aether Catalog definitions — Cryptography_LibraryOfBabel_MiniCatalog
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LibraryOfBabel.MiniCatalog`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LibraryOfBabel/MiniCatalog.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_LibraryOfBabel_Basic
/-
# A de Bruijn Catalog for the Four-Symbol Mini-Library

A cyclic word of length sixteen over four symbols can list every two-symbol
volume exactly once: read the symbol at each position together with its cyclic
successor.  The construction below gives such a word explicitly and proves that
its sixteen cyclic windows form a bijective catalog of the mini-library
`Volume 4 2`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): a four-symbol cyclic volume of length `4^2 = 16` can
catalog all two-symbol volumes without collision, attaining the general counting
bound for windows of length two.

Experiment (Experimenter): the candidate cyclic word
`0010203112132233` produces the windows
`00, 01, 10, 02, 20, 03, 31, 11, 12, 21, 13, 32, 22, 23, 33, 30`.
They are precisely the sixteen ordered pairs over four symbols.

Analysis (Analyst): distinctness of the displayed windows, together with equality
of the finite cardinalities of positions and two-symbol volumes, upgrades the
window map to a bijection.  Thus existence and completeness are separated into
an explicit construction and a structural finite-cardinality argument.

Critique (Critic): this is a cyclic order-two catalog, not a catalog of the
`4^16` books of length sixteen.  Linearizing it requires repeating the initial
symbol, producing length seventeen.  No claim about efficient semantic search
or catalogs of arbitrary order follows from this finite construction.

Synthesis (Principal Investigator): the construction witnesses sharpness of the
capacity bound: all `4^2` reference codes occur once before any cyclic window
repeats.
-/

open Function

namespace LibraryOfBabel

/-- The explicit order-two de Bruijn word `0010203112132233`. -/
def miniCatalog : Fin 16 → Fin 4 := ![0, 0, 1, 0, 2, 0, 3, 1, 1, 2, 1, 3, 2, 2, 3, 3]

/-- Cyclic successor on the sixteen positions of the mini-catalog. -/
def miniNext (i : Fin 16) : Fin 16 := ⟨(i.val + 1) % 16, Nat.mod_lt _ (by omega)⟩

/-- The two-symbol volume named by the cyclic window beginning at `i`. -/
def miniCatalogPair (i : Fin 16) : Volume 4 2 :=
  fun j => if j = 0 then miniCatalog i else miniCatalog (miniNext i)




end LibraryOfBabel


