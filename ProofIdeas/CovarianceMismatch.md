# Covariance Mismatch: freeCovarianceCLM vs freeCovKernel

Date: 2026-03-06

## The Issue

`freeCovarianceCLM` and `freeCovKernel` represent DIFFERENT operators:

- **`freeCovarianceCLM`** (FreeField.lean:114): Uses `GaussianField.spectralCLM` with
  singular values `freeSingularValue mass m = (freeEigenvalue mass m)^{-1/2}`.
  Since `spectralCLM` is diagonal in the Hermite (DyninMityagin) basis, this gives:
  ```
  C(f,g) = Σ_m (1/λ_m) · coeff_m(f) · coeff_m(g)
  ```
  where λ_m = (2n₁+1) + (2n₂+1) + m². This is the resolvent of the
  **harmonic oscillator**: `(-Δ + |x|² + m²)⁻¹`.

- **`freeCovKernel`** (FreeField.lean:176): Defined via the heat kernel integral
  `∫₀^∞ (4πt)⁻¹ exp(-m²t - |x-y|²/(4t)) dt`, which is the Green's function
  of the **flat-space** operator: `(-Δ + m²)⁻¹`.

These are different operators. `gap_covariance_eq_kernel` as stated is **mathematically false**.

## Why the Mismatch Exists

The GaussianField library's `spectralCLM` is diagonal in the DyninMityagin (Hermite)
basis by construction. The only operators that are diagonal in the Hermite basis are
functions of the harmonic oscillator H = -Δ + |x|². The flat-space operator (-Δ + m²)
is NOT a function of H (it equals H - |x|² + m², and |x|² is not diagonal in the
Hermite basis — it's tridiagonal in 1D).

## Physics Consequences

- The harmonic oscillator covariance gives a valid QFT ("field in a harmonic trap")
  but breaks Euclidean translation invariance
- The flat-space covariance gives the standard φ⁴₂ theory with OS axioms
- UV behavior is identical (same logarithmic singularity at short distances)
- IR behavior differs: harmonic trap cures IR divergences, flat-space needs volume cutoff
- To recover the flat-space theory from the harmonic oscillator, take ω → 0 limit
  in C_ω = (-Δ + ω²|x|² + m²)⁻¹

## Resolution Options

### Option A: Accept harmonic oscillator model
- Fix `freeCovKernel` to be the Mehler resolvent kernel (matching `freeCovarianceCLM`)
- Keep flat-space kernel as `flatGreenKernel`
- Document that this is a theory in a trap, not the standard φ⁴₂
- Pro: Simplifies many arguments (no IR divergences)
- Con: Breaks translation invariance, OS axioms don't hold as stated

### Option B: Fix the CLM to be non-diagonal
- Define T : S(ℝ²) → ℓ² as T(f)_m = ⟨ψ_m, (-Δ+m²)^{-1/2} f⟩
- This gives the correct flat-space covariance
- Pro: Correct physics
- Con: Requires substantial functional analysis infrastructure (functional calculus
  for unbounded operators, showing T is a CLM, etc.)

### Option C: Work on a torus
- On a torus of size L, the Fourier basis diagonalizes (-Δ + m²)
- The spectralCLM approach works with Fourier singular values (|k|² + m²)^{-1/2}
- Pro: Standard Glimm-Jaffe approach, correct physics
- Con: Requires switching from Hermite to Fourier basis, changing the DyninMityagin space

### Option D (Recommended): Two-layer approach
- Keep `freeCovarianceCLM` with harmonic oscillator for Gaussian measure construction
  (Wick's theorem, moment formulas, etc.)
- Keep `freeCovKernel` as flat-space for kernel estimates
- Replace `gap_covariance_eq_kernel` with:
  1. A spectral sum formula for the CLM covariance (harmonic oscillator)
  2. A new gap for the kernel bridge that honestly requires non-diagonal CLM or
     the ω → 0 limit
- The key insight: most arguments that use the covariance only need:
  - Gaussian moment structure (from CLM, any covariance works)
  - Kernel bounds (from flat-space kernel, independent of CLM)
  - The bridge is only needed for connecting the two

## Reflection Positivity and the Harmonic Oscillator

Despite the alternating signs in the Hermite expansion (coeff_m(θf) = (-1)^{n₁} coeff_m(f)),
RP DOES hold for the harmonic oscillator covariance. The positive-time support constraint
correlates the Hermite coefficients in exactly the right way.

### Proof Strategy (via 1D Green's function factorization)

1. Decompose in spatial Hermite basis only:
   G(τ₁,x₁; τ₂,x₂) = Σ_{n₂} G_{n₂}(τ₁, τ₂) h_{n₂}(x₁) h_{n₂}(x₂)
2. Each G_{n₂} is the 1D Green's function for -∂_τ² + τ² + μ_{n₂}
3. For the 1D harmonic oscillator with even potential V(τ) = τ², the Green's function
   satisfies: G(-τ₁, τ₂) = (1/W) u₊(τ₁) u₊(τ₂) for τ₁, τ₂ > 0
   (factorization using u₋(τ) = u₊(-τ) for even potentials)
4. This gives: C(θf, f) = Σ_{n₂} (1/W_{n₂}) |∫ f(τ,x) u₊(τ) h_{n₂}(x) dτ dx|² ≥ 0

### Required Infrastructure
- 1D harmonic oscillator Green's function (parabolic cylinder functions)
- Green's function factorization: G(x,y) = (1/W) u₋(min) u₊(max)
- Symmetry: u₋(τ) = u₊(-τ) for even potential
- Integration against spatial Hermite basis

## Current Status

- `gap_covariance_eq_kernel` documented as requiring non-diagonal CLM or ω→0 limit
- `covariance_spectral_sum` proved: the correct spectral formula for the CLM-based covariance
- 1D Green's function factorization infrastructure developed in `GreenFunction/OneDimGreen.lean`:
  - `greenKernel1D_factorization`: G(-s, τ) = (1/(2λ)) exp(-λs) exp(-λτ) for s,τ ≥ 0
  - `greenKernel1D_rp_bilinear_eq_square`: RP bilinear form = (1/(2λ)) (Laplace coeff)²
  - `greenKernel1D_reflection_positive`: non-negativity of the RP bilinear form
- Bridge from 1D RP to the full 2D covariance still needs:
  - Spatial Hermite mode decomposition of the 2D kernel
  - Sum of non-negative terms argument
- Most downstream uses can be refactored to avoid the kernel bridge
