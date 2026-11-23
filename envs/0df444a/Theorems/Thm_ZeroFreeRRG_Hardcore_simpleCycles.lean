-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_simpleCycles
-- name    : ZeroFreeRRG.Hardcore.simpleCycles
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:39:45.241913+00:00
-- url     : https://prove2.me/theorems/18e4bc71-82fb-4ccb-aead-43ab255f16e8
-- title:
--   Simplicity is exactly $X_{1,n}=X_{2,n}=0$
-- statement:
--   A configuration-model pairing $M$ induces a simple $d$-regular graph if and only if
--   $$X_{1,n}(M)=0\quad\text{and}\quad X_{2,n}(M)=0.$$
--   Here $X_{1,n}$ counts self-loops and $X_{2,n}$ counts pairs of parallel edges, exactly as in Definition 3.1. Thus the simplicity event is precisely the conditioning event in reinforced small subgraph conditioning. The statement is pointwise in $n,d$ and needs no parity or size hypothesis.
--
--   **Formalization Note.** `cycleCount M ℓ` divides the number of representing cycle walks by $2\ell$. A self-loop has its two outgoing half-edges as representatives, and a parallel pair has four length-two representatives, so these counts agree with the graph-theoretic events.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510, p. 18 Definition 3.1 and p. 40 (PDF p. 41) proof of Theorem 5.1, sentence 'The simplicity event is X_{1,n}=X_{2,n}=0'.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_AFIsingKS_toGraph
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel

open scoped Classical
open AFIsingKS

/-- Simplicity of a configuration-model pairing is exactly the absence of self-loops and
pairs of parallel edges, i.e. the vanishing of the first two cycle counts. -/
theorem ZeroFreeRRG.Hardcore.simpleCycles {n d : ℕ} (M : Matching n d) :
    IsSimpleM M ↔ cycleCount M 1 = 0 ∧ cycleCount M 2 = 0 := by sorry
