-- Prove2me | Definitions.Def_mme_released_116_integer_profiles
-- name    : mme_released_116_integer_profiles
-- status  : Definition
-- author  : @Robertboy18
-- created : 2026-09-22T13:05:50.412364+00:00
-- url     : https://prove2.me/theorems/c62e0118-19d3-425d-984a-741c54706894
-- title:
--   Integer regional profiles for the released (1,1,6) component
-- statement:
--   Let $d=10^{12}$. For each of the six regions $r$ of the released owner-zero $(1,1,6)$ component, let $b_r$ be its integer region weight, $a_{r,c}$ its split weight, and $u_{r,c,i}(w)$ the mode-$i$ marginal of its square-child counts. Set
--   $$n_r=b_rd^3,\qquad m_{r,c}=b_ra_{r,c}d^2,$$
--   and prescribe child-cell counts
--   $$\mu_i(r,c,w)=b_r(a_{r,c}+a_{r,\bar c})d\,u_{r,c,i}(w).$$
--   Here $\bar c=(1,1,6)-c$ and the four admissible splits are $004,013,103,112$. Child atoms use the released elementary-triple ordering. These are integer data; their mass, support, boundary and normalization properties are separate theorems.

import Definitions.Def_mme_released_116_six_region_reconstruction
import Definitions.Def_mme_released_global_profile_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_yz_owned_filters

open BigOperators
set_option autoImplicit false
namespace MME.Released116
open MoreAsymmetryExactSeed RecursiveYZ CompleteSplit

/-- The parent grade is the released first interior component. -/
def parent : Fin 6 → Fin 3 → ℕ := fun _ => ![1,1,6]

theorem parent_total (r : Fin 6) :
    parent r 0 + parent r 1 + parent r 2 = 2 * 4 := by rfl

abbrev Split := RecursiveThinSplit.Split 4 (parent 0)

/-- Position of a split in the seed's order 004, 013, 103, 112. -/
def splitIndex (c : Split) : ℕ := 2 * (c.val 0).val + (c.val 1).val

def splitWeight (r : Fin 6) (c : Split) : ℕ :=
  (seed.alpha.getD r.val []).getD (splitIndex c) 0

/-- Number of parent occurrences in each region, at scale d^4. -/
def regionalSize (r : Fin 6) : ℕ := seed.region.getD r.val 0 * denominator ^ 3

/-- Exact left-half split counts, retaining the region's alpha row. -/
def splitCount (r : Fin 6) (c : Split) : ℕ :=
  seed.region.getD r.val 0 * splitWeight r c * denominator ^ 2

/-- The mode projection of an encoded square child, using the released
ordering of the six elementary supported triples. -/
def childWord (a : ℕ) (i : Fin 3) : CompleteWord 2 :=
  fun h => ReleasedGlobal.elementary
    ⟨a / 6 ^ h.val % 6, Nat.mod_lt _ (by decide)⟩ i

/-- Marginal child counts before multiplication by the physical cell size. -/
def childMarginal (r : Fin 6) (c : Split) (i : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((child r.val (List.ofFn (fun i => (c.val i).val))).map
    (fun p => if childWord p.1 i = w then p.2 else 0)).sum

/-- Counts at both occurrences of a complementary child cell. The extra
factor d clears the denominator of the child distribution. -/
def integerProfile (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteWord 2) : ℕ :=
  seed.region.getD c.1.val 0 *
    (splitWeight c.1 c.2 + splitWeight c.1 (complement (parent_total c.1) c.2)) *
    denominator * childMarginal c.1 c.2 i w

end MME.Released116


