-- Prove2me | Definitions.Def_BookSixth
-- name    : BookSixth
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-13T01:19:47.067229+00:00
-- url     : https://prove2.me/theorems/b1fcef2b-61fb-4326-bde6-cb6070d37c77
-- title:
--   Sixth-edition theorem interfaces
-- statement:
--   Definitions for the sixth-edition extension of Proofs from THE BOOK: sign matrices, off-diagonal mass, finite Kakeya sets, the row-wise permanent, labeled Latin squares, graph colorings and cycles, genuine round circles and ambient isotopies, good plane drawings with exact crossing records, and explicit Fox coloring equations. The bundle contains definitions and structural constraints only; no book theorem is assumed or proved here. Ambient isotopy and actual edge arcs are part of the mathematical vocabulary, not substitutes for the results to be established.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapters 7, 15, 35, 37, 45. https://doi.org/10.1007/978-3-662-57265-8

import Mathlib

/-! Elementary interfaces for sixth-edition contribution targets.
These definitions contain no claimed book theorems. -/
noncomputable section
open scoped BigOperators
namespace BookSixth

/-- Entries of a real sign matrix are exactly plus or minus one. -/
def SignMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j = 1 ∨ A i j = -1

/-- Squared off-diagonal mass used by the Jacobi reduction. -/
def offDiagonalMass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else (A i j)^2

/-- A finite-field Kakeya set contains a full affine line in each nonzero direction. -/
def Kakeya {F : Type*} [Field F] {n : ℕ} (K : Finset (Fin n → F)) : Prop :=
  ∀ v : Fin n → F, v ≠ 0 → ∃ w : Fin n → F, ∀ t : F, w + t • v ∈ K

/-- Row-wise permanent; choosing one entry in each row using a permutation. -/
def permanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) : ℕ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, A i (σ i)

/-- A labeled Latin square has bijective rows and columns on the fixed alphabet. -/
def Latin {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ (∀ j, Function.Bijective (fun i => L i j))

/-- Number of labeled Latin squares, not isomorphism classes. -/
def latinCount (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun L : Fin n → Fin n → Fin n => Latin L)).card

/-- No clique or independent set of size k in a finite simple graph. -/
def NoMono {N : ℕ} (k : ℕ) (G : SimpleGraph (Fin N)) : Prop :=
  ∀ S : Finset (Fin N), S.card = k →
    (∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ G.Adj u v) ∧
    (∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ¬ G.Adj u v)

/-- A proper coloring by k colors. -/
def HasColoring {N : ℕ} (G : SimpleGraph (Fin N)) (k : ℕ) : Prop :=
  ∃ c : Fin N → Fin k, ∀ u v, G.Adj u v → c u ≠ c v

/-- A simple cycle of length l has distinct cyclically ordered vertices. -/
def HasCycle {N : ℕ} (G : SimpleGraph (Fin N)) (l : ℕ) : Prop :=
  3 ≤ l ∧ ∃ v : Fin l → Fin N, Function.Injective v ∧
    ∀ i j : Fin l, (j.val = (i.val + 1) % l) → G.Adj (v i) (v j)

/-- Three-dimensional real affine space with its usual product topology. -/
abbrev Space3 := Fin 3 → ℝ

/-- Standard separated unit circles used to specify the unlink by ambient isotopy. -/
def standardCircle (i : ℕ) : Set Space3 :=
  Set.range (fun t : ℝ => ![3 * (i : ℝ) + Real.cos t, Real.sin t, 0])

/-- A genuine round circle, described by an orthonormal pair and a positive radius. -/
def RoundCircle (C : Set Space3) : Prop :=
  ∃ c u v : Space3, ∃ r : ℝ, 0 < r ∧
    (∑ i, u i * u i) = 1 ∧ (∑ i, v i * v i) = 1 ∧ (∑ i, u i * v i) = 0 ∧
    C = Set.range (fun t : ℝ => c + (r * Real.cos t) • u + (r * Real.sin t) • v)

/-- An ordered finite link is an unlink when an ambient isotopy takes its components
individually to separated standard circles. Both directions vary continuously. -/
def IsUnlink {m : ℕ} (C : Fin m → Set Space3) : Prop :=
  ∃ H : ℝ → Space3 ≃ₜ Space3,
    Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
    Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
    (∀ x, H 0 x = x) ∧
    ∀ i, (H 1) '' C i = standardCircle i.val

/-- The closed parameter interval for simple plane edge arcs. -/
abbrev EdgeParameter := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}

/-- A good finite plane drawing of a simple graph, with all crossing points recorded.
Edges have distinct unordered endpoint pairs; curves are simple and avoid vertices
in their interiors. The finite crossing set records each interior intersection once
per unordered pair of edges. Adjacent edges have disjoint interiors. -/
structure PlaneDrawing (N M : ℕ) where
  vertex : Fin N → (Fin 2 → ℝ)
  vertex_injective : Function.Injective vertex
  left : Fin M → Fin N
  right : Fin M → Fin N
  no_loop : ∀ e, left e ≠ right e
  no_parallel : ∀ e f, e ≠ f →
    ¬ ((left e = left f ∧ right e = right f) ∨
       (left e = right f ∧ right e = left f))
  arc : Fin M → EdgeParameter → (Fin 2 → ℝ)
  continuous_arc : ∀ e, Continuous (arc e)
  simple_arc : ∀ e, Function.Injective (arc e)
  start : ∀ e, arc e ⟨0, by constructor <;> norm_num⟩ = vertex (left e)
  finish : ∀ e, arc e ⟨1, by constructor <;> norm_num⟩ = vertex (right e)
  avoid_vertices : ∀ e t, 0 < t.val → t.val < 1 → ∀ v, arc e t ≠ vertex v
  crossings : Finset ((Fin M × Fin M) × (Fin 2 → ℝ))
  crossings_exact : ∀ e f x, ((e,f),x) ∈ crossings ↔
    e < f ∧ ∃ t s : EdgeParameter,
      0 < t.val ∧ t.val < 1 ∧ 0 < s.val ∧ s.val < 1 ∧ arc e t = x ∧ arc f s = x
  independent_crossings : ∀ e f x, ((e,f),x) ∈ crossings →
    left e ≠ left f ∧ left e ≠ right f ∧ right e ≠ left f ∧ right e ≠ right f
  no_triple : ∀ e f g (t s u : EdgeParameter),
    0 < t.val → t.val < 1 → 0 < s.val → s.val < 1 → 0 < u.val → u.val < 1 →
    arc e t = arc f s → arc e t = arc g u → e = f ∨ e = g ∨ f = g

/-- The six Fox crossing constraints of the standard Borromean diagram, with
inner labels eliminated using the three outer crossing equations. -/
def BorromeanFox {n : ℕ} (a b c : ZMod n) : Prop :=
  2*(2*b-a) = c+(2*a-c) ∧ 2*(2*c-b) = a+(2*b-a) ∧ 2*(2*a-c) = b+(2*c-b)

/-- Fox constraints of Tait diagram 18 after eliminating its inner arc labels. -/
def TaitFox {n : ℕ} (a : Fin 6 → ZMod n) : Prop :=
  ∀ i : Fin 6, a i - a (i+3) = 4*(a (i+1) - a (i+2))

end BookSixth


