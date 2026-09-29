-- Prove2me | Definitions.Def_Geometry_GravitationalWaves
-- name    : Geometry_GravitationalWaves
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:17:15.311959+00:00
-- url     : https://prove2.me/theorems/c3148ffc-8101-48f4-99f6-b369c848ad5a
-- title:
--   Aether Catalog definitions — Geometry_GravitationalWaves
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.GravitationalWaves`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/GravitationalWaves.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Geometry.SphericalUniverse.GravitationalWaves

Auto-generated from theorem catalog database.
Domain: Geometry/SphericalUniverse
Declarations: 28
-/


noncomputable section

/-- The circumference of S³ with radius R.
A geodesic on S³ is a great circle of length 2πR.
A gravitational wave traveling along a geodesic returns to its source
after traversing one circumference. -/
def circumferenceS3 (R : ℝ) : ℝ := 2 * Real.pi * R








/-- The time delay for a gravitational wave echo in S³.
Δt = circumference / c = 2πR/c
For R ≈ 100 Gly ≈ 3 × 10²⁸ m, c = 3 × 10⁸ m/s:
Δt ≈ 2π × 10²⁰ s ≈ 6 × 10¹² years ≈ 6 trillion years.
This is much longer than the current age of the universe (13.8 Gyr),
so first-order echoes haven't had time to arrive — yet. -/
def echoTimeDelay (R c : ℝ) : ℝ := circumferenceS3 R / c








/-- The n-th echo arrives at time n × Δt. -/
def nthEchoDelay (R c : ℝ) (n : ℕ) : ℝ := n * echoTimeDelay R c












/-- The corresponding frequency for mode n, given speed c.
fₙ = c/λₙ = nc/(2πR) -/
def allowedFrequency (R c : ℝ) (n : ℕ) : ℝ := n * c / (2 * Real.pi * R)








/-- The fundamental frequency (lowest non-zero mode).
f₁ = c/(2πR)
For R = 100 Gly: f₁ ≈ 10⁻²⁰ Hz (far below any detector's range) -/
def fundamentalFrequency (R c : ℝ) : ℝ := c / (2 * Real.pi * R)








/-- The dispersion relation for gravitational waves on S³.
On flat space: ω² = c²k² (continuous)
On S³: ω² = c²(ℓ(ℓ+2))/R² (discrete), ℓ = 0, 1, 2, ...
This is precisely the eigenvalue of the Laplacian on S³!
The Laplacian eigenvalues λₗ = ℓ(ℓ+2)/R² give the squared frequencies. -/
def gwFrequencySquared (R c : ℝ) (ℓ : ℕ) : ℝ :=
  c ^ 2 * (ℓ * (ℓ + 2) : ℝ) / R ^ 2












/-- The energy carried by the n-th GW echo.
As the wave spreads on S³, the energy per solid angle varies.
On S³, the area of a sphere of geodesic radius χ is:
A(χ) = 4πR² sin²(χ/R)
The wave refocuses at the antipodal point (χ = πR) where A → 0,
creating a **conjugate point** (a natural focal point). -/
def areaOnS3 (R χ : ℝ) : ℝ := 4 * Real.pi * R ^ 2 * Real.sin (χ / R) ^ 2




















/-- The number of GW modes in a frequency band [f_low, f_high] on S³.
N = ⌊2πRf_high/c⌋ - ⌊2πRf_low/c⌋
This is finite and computable — a key distinction from flat space
where it would be infinite. -/
def modesInBand (R c f_low f_high : ℝ) : ℤ :=
  ⌊2 * Real.pi * R * f_high / c⌋ - ⌊2 * Real.pi * R * f_low / c⌋
















/-- If a gravitational wave event (e.g., binary neutron star merger) occurs
at geodesic distance χ from us on S³, we observe:
1. Direct signal at time t₁ = χ/c
2. Antipodal echo at time t₂ = (2πR - χ)/c (going the "long way around")
3. Full-circuit echo at time t₃ = (2πR + χ)/c
The time differences give R directly:
t₂ - t₁ = 2(πR - χ)/c
t₃ - t₁ = 2πR/c  (independent of source position!) -/
def directSignalTime (χ c : ℝ) : ℝ := χ / c



/-- [Section: # CatalogBuild.Geometry.SphericalUniverse.GravitationalWaves
Auto-generated from theorem catalog database.
Domain: Geometry/SphericalUniverse
Declarations: 28] -/
def antipodalEchoTime (R χ c : ℝ) : ℝ := (2 * Real.pi * R - χ) / c



/-- [Section: # CatalogBuild.Geometry.SphericalUniverse.GravitationalWaves
Auto-generated from theorem catalog database.
Domain: Geometry/SphericalUniverse
Declarations: 28] -/
def fullCircuitEchoTime (R χ c : ℝ) : ℝ := (2 * Real.pi * R + χ) / c












end


