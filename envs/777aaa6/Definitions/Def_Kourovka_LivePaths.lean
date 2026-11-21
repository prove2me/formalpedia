-- Prove2me | Definitions.Def_Kourovka_LivePaths
-- name    : Kourovka_LivePaths
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:32:07.834637+00:00
-- url     : https://prove2.me/theorems/7e8c9a84-295b-4210-8765-ca7964aeb029
-- title:
--   Live Paths
-- statement:
--   Definitions and structural lemmas for Live Paths, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
set_option autoImplicit true
namespace Kourovka
namespace ProductPaths
variable {A B : Type*} [Group A] [Group B]
def liveDescendants (f : A × B →* A × B) (w : List Bool) : ℕ → Set (List Bool)
  | 0 => {v | v = w ∧ Nonabelian f v}
  | n + 1 => liveDescendants f (w ++ [false]) n ∪ liveDescendants f (w ++ [true]) n
def initialWord (n : ℕ) (x : ℕ → Bool) : List Bool :=
  List.ofFn (FinitePaths.initialSegment n x)
def livePaths (f : A × B →* A × B) : Set (ℕ → Bool) :=
  {x | ∀ n, Nonabelian f (initialWord n x)}
end ProductPaths
end Kourovka


