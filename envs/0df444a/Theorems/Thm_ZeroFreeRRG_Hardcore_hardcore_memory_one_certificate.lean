-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_memory_one_certificate
-- name    : ZeroFreeRRG.Hardcore.hardcore_memory_one_certificate
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:35:12.800619+00:00
-- url     : https://prove2.me/theorems/abe49ead-9696-4326-83b1-e8e1e7b3546e
-- title:
--   A bounded-degree memory-one certificate for the independence polynomial
-- statement:
--   For a graph of maximum degree at most $d$, suppose $0\le c<1$, $p\ge0$, $p(1-c)^{-(d-1)}\le c$, and $p(1-c)^{-d}<1$. Assign $p(1-c)^{-d}$ to each initial state and $c$ to each one-step state. This is a valid memory-one certificate for the independence polynomial. The missing parent neighbor accounts for the exponent $d-1$ in noninitial states.
-- source:
--   Supporting proof of the hardcore zero-free radius in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Graph
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
set_option autoImplicit false
open LocalLemmaHierarchy.Completeness
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_memory_one_certificate {V : Type} [Fintype V] (G : SimpleGraph V) (o : NeighborOrders G)
    (d : ℕ) (hd : 1 ≤ d) (hG : ∀ v, G.degree v ≤ d)
    (p c : ℝ) (hp : 0 ≤ p) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hbulk : p * ((1-c)⁻¹)^(d-1) ≤ c)
    (hroot : p * ((1-c)⁻¹)^d < 1) :
    IsMemCertificate (indRep G o) 1 (fun _ => p)
      (fun s => if s.moves = [] then p*((1-c)⁻¹)^d else c) := by sorry
