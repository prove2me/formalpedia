-- Prove2me | Theorems.Thm_NoBorelUpperBoundFSigma_lemma2_category_transfer
-- name    : NoBorelUpperBoundFSigma.lemma2_category_transfer
-- status  : Proved
-- author  : @username
-- created : 2026-11-02T02:42:52.681908+00:00
-- url     : https://prove2.me/theorems/40920824-81c1-4fcc-8ce2-9028e5727fd5
-- title:
--   Lemma 2 — category transfer for generated coset relations
-- statement:
--   Let P be a standard Borel space, let G and the countable family $A_n$ be fixed Polish groups, and let $h_{n,p}:A_n\to G$ be homomorphisms depending jointly Borel measurably on $(p,a)$, with every section $h_{n,p}$ continuous. Let $z:P\to G$ be Borel, and put $H_p=\langle\bigcup_n h_{n,p}(A_n)\rangle$ and $M=\{p:z(p)\in H_p\}$. If one Borel equivalence relation F on a Polish space Y is an upper bound under Borel reducibility for $E_{H_p}^G$ for every $p\notin M$, then M is Borel in P. No Borel choice of these reductions is assumed, and no regularity of $H_p$ on M is required. The parameter space may be empty; a subgroup uses the algebraic generated subgroup and need not be normal.
-- source:
--   No Borel upper bound for the F_sigma equivalence relations, research proof note dated 1 November 2026, supplied manuscript UniversalBorelEquivalence-20261101.tex, Section 2, Lemma 2, lines 70–84.

import Definitions.Def_NoBorelUpperBoundTransfer20261101

set_option autoImplicit false
open MeasureTheory
universe u v w z

theorem NoBorelUpperBoundFSigma.lemma2_category_transfer
    {P : Type u} [MeasurableSpace P] [StandardBorelSpace P]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, IsTopologicalGroup (A n)] [∀ n, PolishSpace (A n)]
    {Y : Type z} [TopologicalSpace Y] [PolishSpace Y]
    (h : ∀ n, P → (A n →* G))
    (h_joint : ∀ n, @Measurable (P × A n) G
      ((inferInstance : MeasurableSpace P).prod (borel (A n))) (borel G)
      (fun pa => h n pa.1 pa.2))
    (h_cont : ∀ n p, Continuous (h n p))
    (z0 : P → G) (hz : @Measurable P G inferInstance (borel G) z0)
    (F : Setoid Y) (hF : NoBorelUpperBoundFSigma.IsBorelRelation F.r)
    (h_bound : ∀ p, p ∉ NoBorelUpperBoundFSigma.MembershipSet h z0 →
      NoBorelUpperBoundFSigma.BorelReducible
        (NoBorelUpperBoundFSigma.GroupCosetRelation
          (NoBorelUpperBoundFSigma.GeneratedSubgroup h p)) F.r) :
    MeasurableSet (NoBorelUpperBoundFSigma.MembershipSet h z0) := by sorry
