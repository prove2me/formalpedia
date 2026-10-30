-- Prove2me | Definitions.Def_KServer_finite_chunk_certificates
-- name    : KServer_finite_chunk_certificates
-- status  : Definition
-- author  : @kwal0203
-- created : 2026-10-30T02:34:46.407093+00:00
-- url     : https://prove2.me/theorems/0c308c09-07b6-4238-9b21-38b7049ec837
-- title:
--   Finite-horizon online policies and chunk cost certificates
-- statement:
--   For a metric space X and a natural request horizon H, a bounded history is a list of at most H requested subsets of X. A finite-horizon evader policy assigns a point of X to every bounded history and serves every nonempty final request within the horizon. A bailout table assigns a Boolean escape decision to each bounded history.
--
--   When X is finite, the bounded-history domain and the types of policy and bailout tables are finite:
--
--   $$\mathcal H_H=\bigcup_{n=0}^H(2^X)^n,\qquad A:\mathcal H_H\longrightarrow X,\qquad b:\mathcal H_H\longrightarrow\{0,1\}.$$
--
--   The module supplies restrictions of global online policies, total serving extensions of bounded policies, and total bailout-table extensions.
--
--   A finite-horizon chunk certificate has the probabilities, refining filtration, adapted size certificates in the prescribed window, feasible requests, terminal request, offline bound, size window, expected total, and chunk-count constraints of the mission's `ChunkSystemB` model. It additionally records a horizon H bounding the length of every sampled complete request sequence. Its conditional cost tests quantify only over bounded policy and bailout tables; the costs are evaluated through the supplied extensions.
--
--   The horizon bounds the online tests, not the sizes of the real-valued certificates or the complexity of finding a distribution. The structural cost constraints remain separate from the subsequent equivalence theorem.
-- source:
--   Auxiliary finite-horizon formalization of the online-algorithm cost quantifier in Bubeck–Coester–Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4, Lemma 12 and Lemma 15, equation (6), printed pp. 14 and 19–21. The probabilities, filtration, request, size, and online escape clauses follow the existing platform KServer.ChunkSystemB and EvaderAlgorithm.bailCost definitions. Bounded policy tables are an explicitly introduced formalization interface, not a verbatim definition from the paper.

import Definitions.Def_KServer_chunk_system_b

namespace KServer

/-- Histories visible within a fixed request horizon. -/
abbrev BoundedHistory (X : Type*) (H : ℕ) := {l : List (Set X) // l.length ≤ H}

instance boundedHistory_finite {X : Type*} [Finite X] (H : ℕ) :
    Finite (BoundedHistory X H) := by
  let f : BoundedHistory X H → (n : Fin (H + 1)) × List.Vector (Set X) n.val :=
    fun l => ⟨⟨l.val.length, by have := l.property; omega⟩, ⟨l.val, rfl⟩⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun v => v.2.val) hab

/-- An online evader's finite table of positions up to horizon H. -/
structure FiniteEvader (X : Type*) (H : ℕ) where
  pos : BoundedHistory X H → X
  serves : ∀ (l : List (Set X)) (S : Set X) (hl : (l ++ [S]).length ≤ H),
    S.Nonempty → pos ⟨l ++ [S], hl⟩ ∈ S

instance finiteEvader_finite {X : Type*} [Finite X] (H : ℕ) : Finite (FiniteEvader X H) := by
  apply Finite.of_injective (FiniteEvader.pos : FiniteEvader X H → _)
  intro a b hab
  cases a
  cases b
  cases hab
  rfl

noncomputable def FiniteEvader.extend {X : Type*} [MetricSpace X] {H : ℕ}
    (A : FiniteEvader X H) : EvaderAlgorithm X := by
  classical
  exact {
    pos := fun l => if hl : l.length ≤ H then A.pos ⟨l, hl⟩ else
      match l.getLast? with
      | some S => if hS : S.Nonempty then Classical.choose hS else A.pos ⟨[], by simp⟩
      | none => A.pos ⟨[], by simp⟩
    serves := by
      intro l S hS
      by_cases hl : (l ++ [S]).length ≤ H
      · simp only [dif_pos hl]
        exact A.serves l S hl hS
      · simp only [dif_neg hl]
        simpa [hS] using Classical.choose_spec hS }

def EvaderAlgorithm.restrict {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (H : ℕ) : FiniteEvader X H where
  pos l := E.pos l.val
  serves l S _ hS := E.serves l S hS

noncomputable def extendBail {X : Type*} {H : ℕ}
    (b : BoundedHistory X H → Bool) (l : List (Set X)) : Bool := by
  classical
  exact if hl : l.length ≤ H then b ⟨l, hl⟩ else false

/-- A chunk-system certificate whose cost inequalities test only bounded tables. -/
structure FiniteChunkSystemB (X : Type*) [MetricSpace X] (s t : X)
    (cLo cHi total price : ℝ) (mLo : ℕ) where
  Ω : Type
  [instFin : Fintype Ω]
  [instDec : DecidableEq Ω]
  P : Ω → ℝ
  m : ℕ
  H : ℕ
  hist : ℕ → Ω → ℕ
  chunk : Ω → Fin m → List (Set X)
  size : Ω → Fin m → ℝ
  hP : ∀ ω, 0 < P ω
  hPsum : ∑ ω, P ω = 1
  hm : mLo ≤ m
  hm0 : 0 < m
  href : ∀ i j : ℕ, i ≤ j → ∀ ω ω', hist j ω = hist j ω' → hist i ω = hist i ω'
  hadapt : ∀ (i : Fin m) (ω ω' : Ω), hist (i + 1) ω = hist (i + 1) ω' →
    chunk ω i = chunk ω' i
  hsmeas : ∀ (i : Fin m) (ω ω' : Ω), hist i ω = hist i ω' → size ω i = size ω' i
  hne : ∀ ω i, ∀ S ∈ chunk ω i, S.Nonempty
  hlast : ∀ ω, (((List.ofFn (chunk ω)).flatten).getLast?) = some {t}
  hopt : ∀ ω, evaderOfflineCost s ((List.ofFn (chunk ω)).flatten) ≤ dist s t
  hsize : ∀ ω i, cLo ≤ size ω i ∧ size ω i ≤ cHi
  hH : ∀ ω, ((List.ofFn (chunk ω)).flatten).length ≤ H
  hcost : ∀ (i : Fin m) (ω₀ : Ω) (A : FiniteEvader X H)
      (b : BoundedHistory X H → Bool),
    size ω₀ i * (∑ ω ∈ Finset.univ.filter (fun ω => hist i ω = hist i ω₀), P ω)
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => hist i ω = hist i ω₀),
        P ω * A.extend.bailCost (extendBail b)
          (((List.ofFn (chunk ω)).take i).flatten) (chunk ω i) price
  htotal : total ≤ ∑ ω, P ω * (∑ i, size ω i)

attribute [instance] FiniteChunkSystemB.instFin FiniteChunkSystemB.instDec

end KServer


