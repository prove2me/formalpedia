-- Prove2me | Definitions.Def_Evergreen_IdempotentCollapse2_Core
-- name    : Evergreen_IdempotentCollapse2_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:37:33.414364+00:00
-- url     : https://prove2.me/theorems/3369f237-9618-481d-ac81-4fd2e21c9611
-- title:
--   Aether Catalog definitions — Evergreen_IdempotentCollapse2_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.IdempotentCollapse2.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/IdempotentCollapse2/Core.lean by skeleton subtraction
import Mathlib

/-!
# Forced Idempotent Collapse: The Universal Theory

## Can We Collapse Everything?

**Answer: Yes.** Every retraction is an idempotent collapse, and via the axiom
of choice, every nonempty subset admits a retraction — meaning idempotent
collapse is *universally available*.

## Main Results

* `idempotent_image_eq_fixed` — Image of idempotent = fixed points
* `idempotent_iterate_eq` — f^[n] = f for all n ≥ 1
* `universal_collapse_exists` — For any nonempty S ⊆ α, ∃ idempotent f with range f = S
* `universal_forced_collapse` — Full version with hierarchy flatness
* `collapse_inj_on_image` — Collapse is injective on its image
* `total_collapse_exists` — Maximal collapse to a single point
* `identity_unique_total_preserving` — Identity is the unique surjective idempotent
* `collapse_spectrum` — Any intermediate cardinality is achievable
-/

open Set Function

noncomputable section

variable {α : Type*}

/-- An endomorphism is idempotent if applying it twice equals applying it once. -/
def Idempotent (f : α → α) : Prop := ∀ x, f (f x) = f x

/-
PROBLEM
The image of an idempotent equals its fixed-point set.

PROVIDED SOLUTION
ext x. For ⊇: if f x = x then x = f x ∈ range f. For ⊆: if x = f a ∈ range f, then f x = f(f a) = f a = x by hf.
-/


/-
PROBLEM
An idempotent iterated n ≥ 1 times equals itself.

PROVIDED SOLUTION
Induction on n. Base case n=0 contradicts hn. For n+1: if n=0, f^[1]=f trivially. If n≥1, f^[n+1] x = f(f^[n] x) = f(f x) by IH = f x by hf. Use Function.iterate_succ'.
-/

/-
PROBLEM
Composition of two commuting idempotents is idempotent.

PROVIDED SOLUTION
(f∘g)(f∘g)(x) = f(g(f(g(x)))) = f(f(g(g(x)))) by hcomm = f(g(g(x))) by hf = f(g(x)) by hg. So (f∘g)∘(f∘g) = f∘g.
-/












/-- An oracle is an idempotent endomorphism. -/
def IsOracle (O : α → α) : Prop := Idempotent O


/-
PROBLEM
**Collapse Spectrum**: Any intermediate cardinality is achievable on Fin n.

PROVIDED SOLUTION
Define f(i) = if i < m then i else ⟨0, by omega⟩. Then f is idempotent (f(f(i)) = f(i) since f(i) < m) and image = {0,...,m-1} which has cardinality m. Use Fin.val for the condition. The key is constructing f : Fin n → Fin n using fun i => if i.val < m then i else ⟨0, by omega⟩ and showing the image has size m by showing it equals Finset.image Fin.val on {0,..,m-1}.
-/

end


