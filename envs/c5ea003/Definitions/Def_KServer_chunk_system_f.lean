-- Prove2me | Definitions.Def_KServer_chunk_system_f
-- name    : KServer_chunk_system_f
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T09:54:35.285672+00:00
-- url     : https://prove2.me/theorems/c1366001-ce02-4db4-b190-0ee823c6b0ee
-- title:
--   Filtered chunk systems: the BCR Lemma 6 induction package
-- statement:
--   A **filtered chunk system** on a metric space $X$ with marked points $s, t$: the induction package of Bubeck–Coester–Rabani's Lemma 6 (STOC 2023), refining the earlier `KServer_chunk_system` with an **explicit filtration**. Atoms of time-$i$ knowledge are encoded by functions $\mathrm{hist}_i \colon \Omega \to \mathbb{N}$ (as in `KServer_discrete_martingale`); chunk $i$ is revealed at time $i+1$, its size $c_i$ is known at time $i$, and the conditional cost bound — for every deterministic evader, with an escape price on the current chunk — holds on every time-$i$ atom:
--
--   $$c_i \cdot P(A) \;\le\; \sum_{\omega \in A} P(\omega)\, \mathrm{escapeCost}\bigl(\text{past}(\omega), \rho_i(\omega), \text{price}\bigr) \quad \text{for every time-}i\text{ atom } A.$$
--
--   The remaining conditions are as in Lemma 6: nonempty requests, last request $\{t\}$, offline cost at most $d(s,t)$, sizes in $[c_{\mathrm{Lo}}, c_{\mathrm{Hi}}]$, expected total at least `total`, at least $m_{\mathrm{Lo}}$ chunks.
--
--   ## Why the explicit filtration
--
--   BCR's combining step (their Lemma 10) merges consecutive subchunks into larger chunks at data-dependent boundaries; the sizes of the combined chunks are functions of the *underlying subchunk history*, which the combined chunk tuple does not determine (concatenation loses the boundaries). Conditioning on literal past-chunk tuples is therefore not preserved by combining; an abstract refining filtration, of which the chunks are adapted processes, is. Coarser conditional bounds follow from finer ones by summing atoms, so consumers lose nothing.
--
--   ## Formalization note
--
--   All conditional statements are multiplicative over atoms (no division), so mass-zero atoms are harmless.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 6 and Lemma 10.

import Mathlib
import Definitions.Def_KServer_evader

namespace KServer

/-- A **filtered chunk system** on a metric space with marked points `s, t`: a
finitely supported random sequence of `m` chunks of set requests with adapted
sizes, as in BCR's Lemma 6, together with an explicit filtration (atoms encoded
by `hist : ℕ → Ω → ℕ`, refining in time): chunk `i` is revealed at time `i + 1`,
its size is known at time `i`, and the conditional cost bound against every
evader — with an escape price of `price` on the current chunk — holds on every
time-`i` atom. The numeric parameters: sizes lie in `[cLo, cHi]`, the expected
total size is at least `total`, and there are at least `mLo` chunks. -/
structure ChunkSystemF (X : Type*) [MetricSpace X] (s t : X)
    (cLo cHi total price : ℝ) (mLo : ℕ) where
  /-- the finite sample space -/
  Ω : Type
  [instFin : Fintype Ω]
  [instDec : DecidableEq Ω]
  /-- outcome weights -/
  P : Ω → ℝ
  /-- the number of chunks -/
  m : ℕ
  /-- the filtration: time-`i` knowledge, encoded as atoms -/
  hist : ℕ → Ω → ℕ
  /-- the chunks -/
  chunk : Ω → Fin m → List (Set X)
  /-- the sizes -/
  size : Ω → Fin m → ℝ
  hP : ∀ ω, 0 ≤ P ω
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
  hcost : ∀ (i : Fin m) (ω₀ : Ω) (E : EvaderAlgorithm X),
    size ω₀ i * (∑ ω ∈ Finset.univ.filter (fun ω => hist i ω = hist i ω₀), P ω)
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => hist i ω = hist i ω₀),
        P ω * E.escapeCost (((List.ofFn (chunk ω)).take i).flatten) (chunk ω i) price
  htotal : total ≤ ∑ ω, P ω * (∑ i, size ω i)

attribute [instance] ChunkSystemF.instFin ChunkSystemF.instDec

/-- The flattened request sequence of an outcome. -/
def ChunkSystemF.seq {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ}
    {mLo : ℕ} (C : ChunkSystemF X s t cLo cHi total price mLo) (ω : C.Ω) : List (Set X) :=
  (List.ofFn (C.chunk ω)).flatten

end KServer


