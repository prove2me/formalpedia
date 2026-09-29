-- Prove2me | Definitions.Def_MetricTSP_three_paths_seq
-- name    : MetricTSP_three_paths_seq
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-06T01:10:28.941954+00:00
-- url     : https://prove2.me/theorems/fdd4f6d3-b552-4566-9a93-1ebaee8142aa
-- title:
--   Walk parameterisation of the three-paths instance
-- statement:
--   Fix $k \ge 1$ and recall the three-parallel-paths instance on $n = 3k+2$ cities: two hubs $s$ (index $0$) and $t$ (index $3k+1$), joined by three internally disjoint paths each carrying $k$ internal cities, the $i$-th internal city of path $p \in \{0,1,2\}$ being the city with index $1 + pk + (i-1)$.
--
--   `tpSeq k p m` names the $m$-th city encountered when walking path $p$ from $s$ to $t$:
--
--   $$
--   \operatorname{tpSeq}(k,p,m) \;=\;
--   \begin{cases}
--   0 & m = 0 \quad (\text{the hub } s),\\
--   3k+1 & m = k+1 \quad (\text{the hub } t),\\
--   1 + pk + (m-1) & 1 \le m \le k \quad (\text{an internal city of path } p).
--   \end{cases}
--   $$
--
--   The residue in the third branch is inert on the intended range: for $p < 3$ and $1 \le m \le k$ the index $1 + pk + (m-1)$ lies between $1$ and $3k$, so it is already a valid element of `Fin (3*k+2)`; the modulus is present only to supply the bound totally.
--
--   This is the walk-parameterisation of the three-paths instance used when comparing tours and Held–Karp certificates path by path. It is published as a definition module so that theorems about it can be stated with `tpSeq` imported rather than declared inline.
-- source:
--   Companion definition for the three-parallel-paths integrality-gap family; cf. Definitions MetricTSP_model and MetricTSP_three_paths on the platform, and the 4/3 integrality-gap lower bound for the subtour-elimination relaxation.

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths

namespace MetricTSP

/-- The `m`-th city along path `p` of the three-paths instance: the hub `s` at
`m = 0`, the hub `t` at `m = k+1`, and the internal cities in between. -/
def tpSeq (k p m : ℕ) : Fin (3*k+2) :=
  if m = 0 then ⟨0, by omega⟩
  else if m = k+1 then ⟨3*k+1, by omega⟩
  else ⟨(1 + p*k + (m-1)) % (3*k+2), Nat.mod_lt _ (by omega)⟩

end MetricTSP


