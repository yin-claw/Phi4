# Comprehensive Mathematical Reading Note: Glimm-Jaffe φ⁴₂ Construction

**Purpose:** Deep mathematical exposition of the Glimm-Jaffe proof that 2D φ⁴ quantum field theory satisfies the Osterwalder-Schrader axioms, leading via reconstruction to a Wightman QFT. This document provides the technical foundation for supervising the Lean formalization in the Phi4 repository.

**Author:** Claw  
**Date:** 2026-03-28  
**Primary Reference:** Glimm & Jaffe, *Quantum Physics: A Functional Integral Point of View* (2nd ed.)  
**Modern cross-check:** Duch, Dybalski, Jahandideh (2024), arXiv:2311.04137

---

## Part I: Foundations

### 1. The Physical Problem and Strategy

We want to construct a relativistic quantum field theory in 1+1 dimensions (one space, one time) with a scalar field φ and quartic self-interaction. The theory should satisfy:

- **Relativistic invariance** (Poincaré symmetry)
- **Locality** (operators at spacelike separation commute)
- **Spectral condition** (energy-momentum spectrum in forward light cone)
- **Unique vacuum** (ground state)

These are formalized as the **Wightman axioms** (W1-W4).

**Strategy (Euclidean approach):** Rather than constructing Minkowski-signature fields directly, we:

1. Work in **Euclidean signature** (imaginary time τ = it), where QFT becomes classical statistical mechanics
2. Construct a probability measure dμ on field configurations in R²
3. Verify that the correlation functions (Schwinger functions) satisfy the **Osterwalder-Schrader axioms** (OS0-OS4)
4. Apply the **OS reconstruction theorem** to recover a Wightman QFT

**Why Euclidean?** In Euclidean signature:
- The "Boltzmann weight" e^{-V} is a real exponential (not oscillatory)
- Probability measures are easier to construct than oscillatory path integrals
- Classical tools (measure theory, functional analysis, statistical mechanics) apply directly

### 2. The Model

**Free field.** A Gaussian random field φ on R² (really a random tempered distribution in S'(R²)) with covariance
```
C(x,y) = (-Δ + m²)⁻¹(x,y)
```
where Δ is the 2D Laplacian, m > 0 is the mass. The Gaussian measure dφ_C on S'(R²) exists by the Bochner-Minlos theorem.

**Interaction.** The Wick-ordered quartic polynomial, integrated over a finite region Λ ⊂ R²:
```
V_Λ = λ ∫_Λ :φ⁴:(x) dx
```
where λ > 0 is the coupling constant and :φ⁴: denotes Wick ordering (defined below).

**Interacting measure** (finite volume):
```
dμ_Λ = Z_Λ⁻¹ exp(-V_Λ) dφ_C
```
where Z_Λ = ∫ exp(-V_Λ) dφ_C is the partition function.

**The program:**
1. Show exp(-V_Λ) ∈ L¹(dφ_C) so dμ_Λ is a well-defined probability measure
2. Show exp(-V_Λ) ∈ L^p(dφ_C) for all p < ∞ (strong integrability)
3. Take Λ → R² (infinite-volume limit)
4. Verify the OS axioms for the limiting Schwinger functions

### 3. The Osterwalder-Schrader Axioms

Let S_n(f₁,...,f_n) = ∫ φ(f₁)···φ(f_n) dμ be the n-point Schwinger functions and S{f} = ∫ e^{iφ(f)} dμ the generating functional.

**OS0 (Analyticity/Temperedness).** The map z ↦ S{Σ z_j f_j} is entire on C^N for any finite collection f_j ∈ S(R²). Equivalently, S_n are tempered distributions.

**OS1 (Regularity).** There exist c < ∞ and p ∈ [1,2] such that for all f ∈ C₀^∞:
```
|S{f}| ≤ exp(c(‖f‖_{L¹} + ‖f‖_{L^p}^p))
```
For φ⁴, p = 4/3. This controls the growth of the generating functional.

**OS2 (Euclidean Invariance).** S{f} = S{Ef} for all Euclidean motions E (translations, rotations, reflections).

**OS3 (Reflection Positivity).** Let θ: (x,τ) ↦ (x,-τ) be time reflection. For f₁,...,f_N supported in the half-space {τ > 0}, the N×N matrix
```
M_{ij} = S{f_i - θf_j}
```
is positive semidefinite. Equivalently, ⟨θA, A⟩ ≥ 0 for all A in the positive-time algebra.

**Physical meaning of OS3:** This is the Euclidean encoding of **unitarity** — the requirement that the Minkowski Hilbert space has a positive-definite inner product. The Hilbert space of the quantum theory is constructed as H = (E₊ / ker b)^{completion} where b(A,B) = ⟨θA, B⟩ and E₊ is the positive-time function space.

**OS4 (Clustering/Ergodicity).** Time translations act ergodically on (S'(R²), dμ). Equivalently:
```
lim_{t→∞} [S_n(f₁,...,f_k, T_t g₁,...,T_t g_{n-k}) - S_k(f₁,...,f_k)·S_{n-k}(g₁,...,g_{n-k})] = 0
```
where T_t translates by t in the time direction.

**Physical meaning of OS4:** Uniqueness of the vacuum. The connected correlation functions decay at large separations — distant regions are asymptotically independent.

### 4. The OS Reconstruction Theorem

**Theorem (Osterwalder-Schrader).** Given Schwinger functions satisfying OS0-OS4, there exists a unique Wightman QFT satisfying W1-W4 whose vacuum expectation values analytically continue to the given Schwinger functions.

**Construction sketch:**

*Step 1 (Hilbert space).* From the Euclidean measure dμ, form G = L²(S', dμ). Let G₊ = span of functionals of fields at positive times. Define the bilinear form b(A,B) = ⟨θA, B⟩_G. By OS3, b ≥ 0. Set H = (G₊ / ker b)^{completion}.

*Step 2 (Hamiltonian).* Time translation T(t): φ(x,τ) ↦ φ(x,τ+t) induces a map on G₊ (for t ≥ 0). It descends to a contraction semigroup R(t) on H satisfying:
- R(t)R(s) = R(t+s) (semigroup)
- R(t)* = R(t) (self-adjoint, from θ∘T(t) = T(-t)∘θ)
- ‖R(t)‖ ≤ 1 (contraction)
- Strong continuity

By the spectral theorem: R(t) = e^{-tH} with H ≥ 0 self-adjoint.

*Step 3 (Vacuum).* Ω = [1]^hat ∈ H (the class of the constant function 1). Then HΩ = 0.

*Step 4 (Fields).* The Euclidean field operators φ_E(f) (multiplication operators on G) descend to operators Φ_M(f) on H via the Wick rotation t → it. Under OS0-OS3, these are essentially self-adjoint.

*Step 5 (Locality).* Euclidean permutation symmetry (OS3) analytically continues to spacelike commutativity [Φ_M(f), Φ_M(g)] = 0 for f, g with spacelike-separated supports.

*Step 6 (Lorentz covariance).* Euclidean rotation invariance (OS2) analytically continues to Lorentz boost covariance.

*Step 7 (Uniqueness of vacuum).* OS4 (clustering) ⟹ the only vector invariant under time translations is Ω (up to scalar).

### 5. Why Dimension 2 is Critical

The entire construction hinges on controlling the ultraviolet (UV) divergences of the theory. The behavior depends decisively on the spacetime dimension d.

**The free covariance at coincident points.** In momentum space:
```
C_κ(x,x) = ∫_{|p|<κ} d^d p / (2π)^d · 1/(p² + m²)
```

**d = 2 (our case):**
```
C_κ(x,x) = (1/2π) ∫₀^κ 2πp dp/(p² + m²)
          = (1/2π) ln((κ² + m²)/m²)
          ~ (1/π) ln κ   as κ → ∞
```
**Logarithmic divergence.** This is the mildest possible UV divergence.

**d = 3:** C_κ(x,x) ~ κ/(2π²). **Linear divergence.**

**d = 4:** C_κ(x,x) ~ κ²/(4π²). **Quadratic divergence.**

**Why logarithmic is special for φ⁴:**

The Wick-ordered quartic polynomial satisfies:
```
:φ_κ⁴: = (φ_κ² - 3c_κ)² - 6c_κ²  ≥  -6c_κ²
```
where c_κ = C_κ(x,x).

In d = 2: :φ_κ⁴: ≥ -6(ln κ)² — **polynomial in ln κ**

In d ≥ 3: :φ_κ⁴: ≥ -6κ^{2(d-2)} — **exponential in a power of κ**

The crucial estimate (Theorem 8.6.2) requires that the "bad lower bound" from semiboundedness be overwhelmed by the "good upper bound" from Gaussian concentration. In d = 2, the lower bound grows as (ln κ)² while the Gaussian tail decays as exp(-κ^ε). Exponential beats polynomial — the integral converges.

In d ≥ 3, both bounds are exponential in powers of κ, and the integral cannot be controlled by Wick ordering alone. One needs **mass renormalization** (adding a κ-dependent mass counterterm δm²(κ)φ² to the interaction) to restore the balance.

**Conclusion:** In d = 2, Wick ordering is the only renormalization needed. This makes φ⁴₂ the simplest interacting QFT to construct rigorously, and the natural first target for formalization.

---

## Part II: Gaussian Foundations (Chapters 6-7)

### 6. The Free Gaussian Measure

**Construction.** The Gaussian measure dφ_C on S'(R²) is characterized by its generating functional:
```
∫ exp(iφ(f)) dφ_C = exp(-½⟨f, Cf⟩)
```
where ⟨f, Cf⟩ = ∫∫ f(x) C(x,y) f(y) dx dy.

**Moments (Wick/Isserlis theorem):**
```
∫ φ(f₁)···φ(f_{2n}) dφ_C = Σ_{pairings π} ∏_{(i,j)∈π} ⟨f_i, Cf_j⟩
∫ φ(f₁)···φ(f_{2n+1}) dφ_C = 0
```
The sum is over all perfect pairings of {1,...,2n}. There are (2n-1)!! = (2n-1)(2n-3)···1 terms.

**Integration by parts (Theorem 6.3.1):**
```
∫ φ(f) A(φ) dφ_C = ∫ ⟨f, C · δA/δφ⟩ dφ_C
```
where δA/δφ is the functional derivative. This is the fundamental identity for Gaussian measures.

### 7. Covariance Operators and Boundary Conditions

The covariance C = (-Δ + m²)⁻¹ has a kernel:
```
C(x,y) = (2π)⁻¹ K₀(m|x-y|)
```
where K₀ is the modified Bessel function of the second kind. Key properties:

**Logarithmic singularity at short distance (d=2):**
```
C(x,y) ~ -(2π)⁻¹ ln(m|x-y|)   as |x-y| → 0
```

**Exponential decay at long distance:**
```
C(x,y) ~ const · (m|x-y|)⁻¹/² exp(-m|x-y|)   as |x-y| → ∞
```

The exponential decay C(x,y) ~ e^{-m|x-y|} is **essential** throughout the construction. It ensures distant regions are nearly independent.

**Boundary conditions and the fundamental ordering.** For a region Λ with boundary conditions B:

| BC type | Covariance C_B | Method |
|---------|---------------|--------|
| Free (no BC) | C = (-Δ+m²)⁻¹ | Full-space Green's function |
| Periodic | C_P(x,y) = Σ_{nL} C(x-y+nL) | Method of images (sum) |
| Neumann | C_N(x,y) = Σ_j C(x-y_j) | Method of images (sum, all +) |
| Dirichlet | C_D(x,y) = Σ_j (-1)^{σ_j} C(x-y_j) | Method of images (alternating ±) |

**Fundamental ordering (Proposition 7.7.1):**
```
0 ≤ C_D ≤ C ≤ C_N ≤ C_P
```

**Proof of C_D ≤ C:** By maximum principle. u(x) = C(x,y) - C_D(x,y) satisfies (-Δ+m²)u = 0 in Λ with u > 0 on ∂Λ. Maximum principle: u > 0 everywhere.

Alternative: Form domain argument. D(-Δ_D) ⊂ D(-Δ) (Dirichlet restricts the variational space). Since -Δ_D ≥ -Δ as quadratic forms, inverting reverses the inequality: C_D ≤ C.

**Monotonicity in domain (Dirichlet).** If Λ₁ ⊂ Λ₂, then C^D_{Λ₁} ≤ C^D_{Λ₂} (enlarging the domain increases the Dirichlet covariance). This is crucial for the monotonicity argument in the infinite-volume limit.

**Reflection positivity of the covariance.** Let θ: (x,τ) ↦ (x,-τ) be time reflection, and Π = {τ = 0} the reflection hyperplane. Then C is **reflection-positive**: for f supported at τ > 0,
```
⟨θf, Cf⟩ ≥ 0
```

**Proof:** Decompose C into half-space contributions using Dirichlet at Π:
```
⟨θf, Cf⟩ = ⟨θf, (C - C_D)f⟩ + ⟨θf, C_D f⟩
```
The second term vanishes (C_D decouples across Π). The first is ≥ 0 because C - C_D ≥ 0 and has specific positivity structure from the kernel formula:
```
(C - C_D)(x,y) = ∫₀^∞ e^{-m²t} K_D(t; x,y) dt
```
where K_D is the heat kernel reflected at Π, which satisfies K_D(t; θx, y) = K_D(t; x, θy) ≥ 0 when both x, y have τ > 0.

More explicitly:
```
⟨θf, Cf⟩ = ½⟨g, μ⁻¹ e^{-2μ|τ₁+τ₂|} g⟩ ≥ 0   for f = g(x)δ(τ - τ₁)
```
where μ = (-Δ_{d-1} + m²)^{1/2}.

### 8. Wick Ordering

**Problem:** For a distribution-valued field φ, pointwise products like φ(x)⁴ are undefined.

**Solution:** Use regularized fields φ_κ(x) = (h_κ * φ)(x) where h_κ is a UV cutoff (mollifier at scale 1/κ). Then define:

```
:φ_κ^n:(x) = c_κ^{n/2} H_n(φ_κ(x)/c_κ^{1/2})
```
where H_n is the n-th (probabilist's) Hermite polynomial and c_κ = C_κ(x,x) = ⟨h_κ(·-x), C h_κ(·-x)⟩.

**Explicit formulas:**
```
:φ⁰: = 1
:φ¹: = φ
:φ²: = φ² - c_κ
:φ³: = φ³ - 3c_κ φ
:φ⁴: = φ⁴ - 6c_κ φ² + 3c_κ²
```

**Key algebraic identity (completing the square):**
```
:φ⁴:_κ = (φ_κ² - 3c_κ)² - 6c_κ²
```
This shows :φ⁴: ≥ -6c_κ² (semiboundedness).

**Orthogonality under the Gaussian measure:**
```
∫ :φ^n:(f) :φ^m:(g) dφ_C = δ_{nm} · n! · ⟨f,Cg⟩^n
```
This follows from Hermite polynomial orthogonality.

**UV limit:** As κ → ∞, :φ_κ^n:(f) → :φ^n:(f) in L²(dφ_C) for suitable f. The limit is Wick-ordering-convention-independent (the standard Wick product).

### 9. Wick's Theorem and Feynman Graphs

**Wick's theorem (exact Gaussian integral decomposition):**
```
∫ ∏ᵢ :φ^{nᵢ}:(fᵢ) dφ_C = Σ_G I(G)
```
where the sum is over all Feynman graphs G with nᵢ legs at vertex i, and
```
I(G) = ∫ [∏_{lines l} C(x_{l₁}, x_{l₂})] · [∏_i fᵢ(xᵢ)] · ∏ dxᵢ
```

**Two types of lines:**
- **Self-lines (S):** Both endpoints at the same vertex → contribute δC = C_wick - C_integration
- **Interaction lines (I):** Endpoints at different vertices → contribute C

**Crucial fact:** When the Wick ordering covariance equals the integration covariance, all self-lines give δC = 0. Only interaction lines survive. This eliminates vacuum bubble contributions.

**Non-perturbative character:** This is NOT perturbation theory in the coupling constant λ. Wick's theorem is an exact identity for Gaussian integrals. The sum over all graphs is finite (for suitable integrands) and can be bounded non-perturbatively.

### 10. Localized Graph Bounds (Theorem 8.5.5)

This is the **single most important estimate** in the entire construction. It feeds into:
- WP1: L^p integrability of exp(-V)
- WP2: Chessboard/multiple reflection bounds  
- WP4: Integration-by-parts bounds in the regularity proof

**Statement.** Let G be a graph with vertices localized in unit squares Δᵢ. Let N(Δ) count the total number of legs in square Δ. Then:
```
|I(G)| ≤ ‖w‖_{L^p} · ∏_Δ N(Δ)! · (const/m)^{N(Δ)}
```

**Key features:**
- **Per-square factorials:** N(Δ)! not (ΣN(Δ))! — the graph integral factorizes over localized regions
- **Exponential decorrelation:** The mass m provides exp(-m·distance) between squares, absorbed into the (const/m)^N(Δ) factor

**Proof sketch.** Hölder's inequality applied to the graph integral. The key input is the L^q bound on the covariance kernel restricted to unit squares:
```
‖C(·,·)|_{Δᵢ × Δⱼ}‖_{L^q} ≤ const · m^{-1/q} · e^{-m·dist(Δᵢ,Δⱼ)}
```
The exponential decay in distance between squares means contributions from distant pairs of squares are exponentially suppressed. After Hölder and combinatorial counting, one obtains the per-square factorial bound.

**Why per-square factorials are manageable.** If each unit square has at most N legs, the total graph bound is ∏_Δ N(Δ)!. For the φ⁴ interaction localized in Λ with n vertices, the dominant configuration has ~n/|Λ| vertices per square, giving:
```
∏_{Δ ⊂ Λ} (4n/|Λ|)! ~ exp(n ln n - n ln |Λ|)
```
This is manageable when combined with the combinatorial prefactor 1/n! from the exponential.

---

## Part III: Finite-Volume Construction (Chapter 8, WP1) — The Critical Path

### 11. The Main Integrability Theorem (Theorem 8.6.2)

**Statement:** For C₁, C₂ ∈ C_m (the convex class of covariances with mass ≥ m), f satisfying conditions (8.6.4), and P a polynomial bounded below:
```
∫ exp(-:P(φ,f):_{C₁}) dφ_{C₂} ≤ exp(const(N(f) + 1))
```
where N(f) is a polynomial seminorm of f.

For φ⁴ specifically (P(φ) = λφ⁴, f = χ_Λ):
```
∫ exp(-λ∫_Λ :φ⁴: dx) dφ_C ≤ exp(const · |Λ|)
```

**Significance:** This is THE central analytic estimate. It says:
1. exp(-V_Λ) ∈ L^p(dφ_C) for all p < ∞
2. The partition function Z_Λ = ∫ exp(-V_Λ) dφ_C is finite and positive
3. The interacting measure dμ_Λ = Z_Λ⁻¹ exp(-V_Λ) dφ_C is well-defined
4. The bound is linear in |Λ|, enabling the infinite-volume limit

### 12. Proof of Theorem 8.6.2: The Two-Step Strategy

The proof combines two complementary estimates:

**Step 1: Semiboundedness (Proposition 8.6.3).**

For the regularized (UV cutoff κ) Wick polynomial:
```
:φ_κ⁴:_C ≥ -6c_κ² = -6[C_κ(x,x)]²
```

**Proof:** Direct algebra.
```
:φ_κ⁴:_C = φ_κ⁴ - 6c_κ φ_κ² + 3c_κ²        [definition of Wick ordering]
          = (φ_κ² - 3c_κ)² - 9c_κ² + 3c_κ²   [completing the square]
          = (φ_κ² - 3c_κ)² - 6c_κ²
          ≥ -6c_κ²                              [square ≥ 0]
```

In d = 2: c_κ ~ (2π)⁻¹ ln κ, so:
```
:φ_κ⁴: ≥ -6/(2π)² · (ln κ)² ≥ -const · (ln κ)²
```

**Consequence for the interaction:**
```
V_{Λ,κ} = λ∫_Λ :φ_κ⁴: dx ≥ -6λc_κ² |Λ| = -const · |Λ| · (ln κ)²
```
Therefore:
```
exp(-V_{Λ,κ}) ≤ exp(const · |Λ| · (ln κ)²)
```
This is a polynomial bound in κ (since (ln κ)² grows slower than any power of κ).

**Step 2: Small Bad Set Estimate (Proposition 8.6.4).**

Let δP_κ = :P(φ):_C - :P(φ_κ):_C be the "UV remainder" (difference between the true and regularized Wick polynomials). Let χ(κ) = {φ : |δP_κ(φ,f)| ≥ 1}. Then:
```
μ_C(χ(κ)) ≤ exp(-α(κ^ε / M(f))^{2/deg P})
```
where α > 0, ε > 0, and M(f) depends on f.

**Proof:** Chebyshev inequality + moment optimization.

*Step 2a:* Bound the 2j-th moment of δP_κ using Theorem 8.5.3 (Gaussian integral estimates from Feynman graphs):
```
∫ |δP_κ(φ,f)|^{2j} dφ_C ≤ (2j)!^{n/2} · (const · ‖f‖_{L^p} · κ^{-ε})^{2j}
```
where n = deg P = 4 for φ⁴.

*Step 2b:* Apply Chebyshev:
```
μ_C(χ(κ)) ≤ ∫ |δP_κ|^{2j} dφ_C ≤ [(2j)!^2 · (const κ^{-ε})^{2j}]
```

*Step 2c:* Optimize over j. Using Stirling: (2j)! ~ (2j/e)^{2j}, so:
```
μ_C(χ(κ)) ≤ [(const · j / e)^{2} · κ^{-ε}]^{2j}
```
Choose j ~ κ^{ε/2} to minimize:
```
μ_C(χ(κ)) ≤ exp(-const · κ^ε)
```

This is the **double-exponential tail bound**: the probability of a large UV remainder decays faster than any polynomial in κ.

**Combining Steps 1 and 2: Layer-cake integration.**

We want to bound ∫ exp(-pV_Λ) dφ_C for arbitrary p. Split the integration domain:

*Good set (φ close to its cutoff approximation):*
On {|δP_κ| < 1}, we have V_Λ ≈ V_{Λ,κ} + O(|Λ|), so:
```
exp(-pV_Λ) ≤ exp(-pV_{Λ,κ} + p|Λ|) ≤ exp(p · const · |Λ| · (ln κ)² + p|Λ|)
```
using the semiboundedness from Step 1.

*Bad set (φ far from cutoff approximation):*
The measure of the bad set is at most exp(-const · κ^ε) from Step 2.

*Optimizing κ:* Choose κ such that the polynomial bound from the good set and the exponential tail from the bad set balance optimally. The exponential always wins, giving:
```
∫ exp(-pV_Λ) dφ_C ≤ exp(const · p · |Λ|)
```

More precisely, the layer-cake formula gives:
```
∫ |g|^p dμ = p ∫₀^∞ a^{p-1} μ{|g| > a} da
```
Applying this with g = exp(-V_Λ):
- For large a: μ{exp(-V_Λ) > a} = μ{V_Λ < -ln a}. By semiboundedness, V_Λ ≥ -const |Λ|(ln κ)², so for a > exp(const |Λ|(ln κ)²), the set is empty.
- For moderate a: μ{V_Λ < -ln a} ≤ μ{|δP_κ| ≥ ε₀} ≤ exp(-const κ^ε) from the small bad set.
- The integral converges because the exponential tail beats the polynomial growth.

### 13. The Shell Estimates (WP1, Branch 1)

The shell estimates control the **UV cutoff sequence convergence** — showing that the regularized interaction V_{Λ,κ} converges to V_Λ as κ → ∞.

**Dyadic shell decomposition.** Let κ_n = 2^n. The difference between successive cutoffs is:
```
V_{Λ,κ_{n+1}} - V_{Λ,κ_n} = λ∫_Λ [:φ_{κ_{n+1}}⁴: - :φ_{κ_n}⁴:] dx
```

This difference involves only the "shell" modes with κ_n ≤ |p| ≤ κ_{n+1}.

**Gap 10 (gap_wickPowerStandardSeqShellUpper_spatial_sq_rate):** The root of the shell branch. Statement: the L² norm of the shell-side Wick power contribution has a specific spatial decay rate.

**Mathematical content:** For the shell between cutoffs κ_n and κ_{n+1}:
```
‖:φ_{κ_{n+1}}^4: - :φ_{κ_n}^4:‖²_{L²(dφ_C)} 
= Σ_G |I(G)|²
```
where the graphs G have vertices in the shell. The key is that shell contributions have better decay properties than full contributions, because the shell covariance δC_n(x,y) = C_{κ_{n+1}}(x,y) - C_{κ_n}(x,y) has faster decay in |x-y| than C itself (the shell modes are higher-frequency, hence more localized).

**Proof idea:** Localized graph bounds (Theorem 8.5.5) applied to the shell covariance. The shell covariance satisfies:
```
|δC_n(x,y)| ≤ const · 2^{-nε} · e^{-m|x-y|}
```
for some ε > 0, giving improved decay for each successive shell.

**Why this matters:** Once gap 10 is proved, gaps 11-14 follow in a chain:
- Gap 11: Quartic shell rate (from gap 10 by summation)
- Gap 12: Discrete cutoff L² increment rate (from gap 11)
- Gap 13: Summable L¹ increments (from gap 12 by Cauchy-Schwarz)
- Gap 14: a.e. convergence (from gap 13 by Borel-Cantelli)

### 14. The Nelson Bound (WP1, Branch 2)

The Nelson bound controls the **double-exponential tail** — the probability that the interaction V_Λ takes extremely large values.

**Historical context:** Edward Nelson introduced hypercontractivity (L^p improvement of the Gaussian semigroup) as a tool for constructing QFTs. The Nelson bound is the culmination of this approach.

**Gap 19 (gap_regularizedPointCovariance_log_growth):** THE KEY d=2 FACT.

Statement: There exist K, C₀ > 0 such that for all UV cutoffs κ:
```
regularizedPointCovariance(m, κ) ≤ C₀ + K · ln κ
```

This is the formalization of c_κ ~ ln κ.

**Proof:** Direct calculation from the definition:
```
c_κ = ∫∫ h_κ(x) C(x,y) h_κ(y) dx dy
```
where h_κ is the UV mollifier. In momentum space:
```
c_κ = ∫ |ĥ(p/κ)|² / (p² + m²) · d²p/(2π)²
```
Split into |p| ≤ κ (contributes ~ ln κ) and |p| > κ (contributes O(1)). The mollifier ĥ(p/κ) ≈ 1 for |p| ≪ κ and decays for |p| ≫ κ.

**In the Lean code:** This gap depends on two sub-gaps:
- `gap_uvMollifier_covariance_eq_freeCovKernel`: The CLM covariance matches the kernel covariance when smeared against mollifiers
- `gap_uvMollifier_freeCovKernel_log_growth`: The kernel-level estimate ∫∫ h_κ C h_κ ≤ C₀ + K ln κ

Both are in FreeField.lean and are currently sorry'd.

**Gap 22 (gap_finiteWickCylinder_even_moment_comparison):** Hypercontractive comparison.

Statement: For finite Wick cylinders (finite-dimensional approximations to :φ⁴:), the even moments satisfy a comparison bound derived from Nelson's hypercontractivity.

**Nelson's hypercontractivity (Theorem, Simon-Hoegh-Krohn 1972):** For the Gaussian semigroup P_t = e^{-tN} (where N is the number operator):
```
‖P_t‖_{L^p → L^q} ≤ 1   when q-1 ≤ (p-1)e^{2t}
```

This means the Gaussian semigroup improves L^p regularity over time. Applied to Wick powers:
```
‖:φ^n:‖_{L^q(dφ_C)} ≤ (q-1)^{n/2} ‖:φ^n:‖_{L^2(dφ_C)}
```

**Why hypercontractivity matters for the tail bound:** The even-moment comparison (gap 22) feeds into gaps 23 → 24 → 26 → 27 → 28, ultimately giving the double-exponential tail:
```
μ{V_Λ < -K} ≤ exp(-exp(const · K^{1/2}))
```

This decay is so fast that it controls all polynomial growth from semiboundedness.

**Gap 25 (gap_interactionCutoff_reference_shell_L2_bound):** Reference-shell L² decay.

Statement: A specific reference-shell contribution has controlled L² norm.

**Proof idea:** Again uses localized graph bounds, but for a specific "reference" shell chosen to optimize the Nelson bound.

### 15. How the Two Branches Merge

The shell estimates (gaps 10-14) and the Nelson bound (gaps 19, 22-28) are **independent** branches that must both be completed for the WP1 endpoint.

**Branch 1 output:** V_{Λ,κ} → V_Λ in L²(dφ_C) as κ → ∞ (UV convergence).

**Branch 2 output:** exp(-pV_Λ) has controlled moments for all p (double-exponential tail + semiboundedness).

**WP1 endpoint (gap 29, gap_hasExpInteractionLp):** Combines both branches via:
```
∫ exp(-pV_Λ) dφ_C ≤ exp(const · p · |Λ|)
```

This is now proved in the Lean code **modulo** the branch gaps. The file `Interaction/AnalyticInputs.lean` assembles the final theorem from the two branch outputs.

---

## Part IV: Correlation Inequalities and Reflection Positivity (Chapters 9-10, WP2)

### 16. Lattice Approximation (Chapter 9)

The correlation inequalities are first proved for **lattice spin systems** (finite-dimensional integrals), then transferred to the continuum via approximation.

**Lattice model.** Replace R² by a lattice Λ_δ = δZ² ∩ Λ. The field becomes a finite collection of real variables {φ_x}_{x ∈ Λ_δ}. The measure is:
```
dμ_δ = Z⁻¹ exp(-Σ_{⟨x,y⟩} J_{xy}(φ_x - φ_y)² - Σ_x P(φ_x)) ∏_x dφ_x
```

**Continuum limit (Proposition 9.1.2):** As δ → 0:
- Lattice Schwinger functions → continuum Schwinger functions
- Lattice partition functions → continuum partition function
- Lattice correlation inequalities → continuum correlation inequalities

### 17. GKS Inequalities

**GKS-I (Griffiths, Kelly, Sherman):** For P = even polynomial − μφ with μ ≥ 0:
```
⟨φ_{A}⟩ ≥ 0   for all A ⊂ Λ_δ
```
where φ_A = ∏_{x ∈ A} φ_x.

**Proof sketch (lattice).** The measure dμ can be written as a product of ferromagnetic factors (each factor is a function of a single "bond" variable). Each factor preserves non-negativity of moments. By the Griffiths trick (expanding in elementary positive functions), all moments are non-negative.

**GKS-II (Truncated pair correlation positivity):**
```
⟨φ_A φ_B⟩ - ⟨φ_A⟩⟨φ_B⟩ ≥ 0
```

**Proof (lattice).** Duplication trick: introduce independent copies (φ, χ) with joint measure dμ(φ)dμ(χ). Define t = (φ+χ)/√2, q = (φ-χ)/√2. Then:
```
⟨φ_A φ_B⟩ - ⟨φ_A⟩⟨φ_B⟩ = ⟨(φ_A - χ_A)(φ_B - χ_B)⟩_{φ,χ}
```
Express in (t,q) variables and apply GKS-I to the doubled system.

**Physical significance of GKS-II:** Increasing the coupling (or the volume) can only increase correlations. This gives **monotonicity** of Schwinger functions in the volume Λ.

**FKG inequality:** For semibounded P and monotone functions F, G (both increasing or both decreasing):
```
⟨FG⟩ ≥ ⟨F⟩⟨G⟩
```

**Lebowitz inequality:** For P = λφ⁴ + σφ² - μφ, the connected 4-point function (Ursell function) is non-positive:
```
U₄(x₁,x₂,x₃,x₄) ≤ 0
```
where U₄ = S₄ - S₂(1,2)S₂(3,4) - S₂(1,3)S₂(2,4) - S₂(1,4)S₂(2,3).

### 18. Reflection Positivity for the Interacting Measure

**Theorem 10.4.3.** If:
1. dφ_C is reflection-positive (θ-invariant covariance)
2. V = V₊ + V₋ with V₊ supported at τ > 0 and θV₊ = V₋
3. θΛ = Λ (symmetric volume)

Then dμ_Λ = Z⁻¹ exp(-V) dφ_C is reflection-positive.

**Proof.** For A ∈ A₊ (positive-time observable):
```
⟨θA, A⟩_{dμ} = Z⁻¹ ∫ (θA)* · A · exp(-V₊ - V₋) dφ_C
              = Z⁻¹ ∫ (θA)* · A · exp(-V₊ - θV₊) dφ_C
              = Z⁻¹ ∫ [θ(A · e^{-V₊})]* · [A · e^{-V₊}] dφ_C
              ≥ 0
```
The last step uses RP of dφ_C, applied to the positive-time functional A · e^{-V₊}.

**Key point:** RP is preserved under limits (it's a positivity condition on a bilinear form, which is closed under limits). So the infinite-volume measure dμ is also RP.

### 19. Multiple Reflections and Chessboard Estimates (Section 10.5)

**The chessboard estimate** is an iterated application of reflection positivity across a lattice of hyperplanes.

**Setup.** Let Λ = [0,L]² be a square, tiled by unit squares Δ_α. For each unit square, choose a local observable k^{(α)} supported in Δ_α.

**Chessboard estimate (Corollary 10.5.8):**
```
|∫ ∏_{α} k^{(α)} dμ_Λ| ≤ ∏_{α} L(k^{(α)})
```
where L(k) is the "reflected norm":
```
L(k) = lim_{n→∞} [∫ R_n(k) dμ_Λ]^{1/2ⁿ}
```
and R_n(k) is the 2ⁿ-fold reflection of k.

**Proof by iterated Schwarz inequality:**

*d=1 version (one reflection):*
```
|∫ k dμ|² ≤ ∫ (θk)* · k dμ        [by RP]
```

*d=2 version (two orthogonal reflections):*
```
|∫ k dμ|² ≤ ∫ (θ_x k)* · k dμ     [RP in x-direction]
|∫ (θ_x k)* · k dμ|² ≤ ∫ R(k) dμ  [RP in y-direction]
```
Combining: |∫ k dμ|⁴ ≤ ∫ R(k) dμ where R(k) = (θ_x θ_y k)*(θ_y k)(θ_x k)*k.

*General:* Iterate n times in each direction to get:
```
|∫ k dμ|^{2^{2n}} ≤ ∫ R_n(k) dμ
```

**Why this is useful:** The chessboard estimate reduces a **global** bound (over the full volume Λ) to **per-square** bounds (over unit squares). Combined with Theorem 8.6.2 (which bounds exp(-V) per unit square), this gives the uniform volume-independent bounds needed for the infinite-volume limit.

---

## Part V: Infinite-Volume Limit (Chapter 11, WP3)

### 20. Monotonicity and the Existence Theorem

**Theorem 11.2.1 (Infinite-volume limit existence).** For P = even polynomial + linear term:
```
S{f} = lim_{Λ→R²} S_Λ{f} exists
```
and satisfies OS0, OS2, OS3.

**Proof: Three ingredients.**

*Ingredient 1: Monotonicity.* For real-valued non-negative g, the Schwinger function S_Λ{-ig} = ⟨e^{φ(g)}⟩_Λ is monotone increasing in Λ.

**Proof of monotonicity:** For Λ₁ ⊂ Λ₂:
1. **Covariance monotonicity:** C^D_{Λ₁} ≤ C^D_{Λ₂} (domain monotonicity of Dirichlet covariance)
2. **GKS-II:** For the interacting measure with Dirichlet BC, increasing the covariance increases all correlations
3. **Therefore:** S^{Λ₁}(g) ≤ S^{Λ₂}(g) for g ≥ 0

*Ingredient 2: Uniform upper bound (Theorem 11.3.1).* For f ∈ L¹ ∩ L^p supported in compact K:
```
|S_Λ{f}| ≤ exp(c(|K| + ‖f‖_{L^p}^p))
```
**independent of Λ.**

This is the hardest estimate in WP3. Its proof uses the chessboard estimate (Section 10.5) combined with Theorem 8.6.2. See Section 21 below.

*Ingredient 3: Vitali's theorem (analytic extension).* S_Λ{zg} is entire in z (analytic on all of C) for g ≥ 0. The family {S_Λ{z·}} is uniformly bounded (from Ingredient 2). From Ingredient 1, S_Λ{zg} converges for z ∈ R₊. Vitali's theorem extends convergence to all z ∈ C.

**Vitali's theorem:** If {f_n} is a sequence of analytic functions on a domain D, uniformly bounded on compact subsets of D, and converging pointwise on a subset E with an accumulation point in D, then f_n → f uniformly on compact subsets of D, and f is analytic.

### 21. Proof of the Uniform Bound (Theorem 11.3.1)

This is the most technically demanding estimate in WP3. The proof uses **asymmetric multiple reflections** combined with **conditioning** on boundary conditions.

**Setup.** Want to bound ∫ e^{φ(f)} dμ_Λ for f supported in compact K.

**Step 1: Enlargement.** Choose Λ^{(0)} ⊃ Λ centered at a corner of K.

**Step 2: Reflection.** Apply RP in two orthogonal directions:
```
|∫ e^{φ(f)} dμ_{Λ^{(0)}}|⁴ ≤ ∫ e^{φ(f^{(1)})} dμ_{Λ^{(1)}}
```
where f^{(1)} = (1+θ_x)(1+θ_y)f has support K^{(1)} of area 4|K|, and Λ^{(1)} ⊃ Λ^{(0)}.

**Step 3: Iterate n times.** After n iterations:
```
|∫ e^{φ(f)} dμ_{Λ^{(0)}}|^{4ⁿ} ≤ ∫ e^{φ(f^{(n)})} dμ_{Λ^{(n)}}
```
with |K^{(n)}| = 4ⁿ|K| and ‖f^{(n)}‖_{L^p}^p = 4ⁿ‖f‖_{L^p}^p.

**Step 4: Terminate when K^{(n)} fills Λ^{(n)}.**

**Step 5: Switch to Neumann BC.** Replace Dirichlet by Neumann on a unit lattice tiling Λ^{(n)}. Since C_D ≤ C_N, and the Neumann covariance factorizes:
```
Z_N(Λ) = ∏_{Δ ∈ tiling} Z_N(Δ)
```

**Step 6: Per-square bound.** Apply Theorem 8.6.2 to each unit square Δ:
```
∫_{Δ} e^{φ(f^{(n)}_Δ)} dμ_N ≤ exp(c(1 + ‖f^{(n)}_Δ‖_{L^p}^p))
```

**Step 7: Combine.** The total bound is:
```
|∫ e^{φ(f)} dμ_Λ| ≤ [∏_Δ exp(c(1 + ‖f^{(n)}_Δ‖))]^{4^{-n}}
                   = exp(4^{-n} · Σ_Δ c(1 + ‖f^{(n)}_Δ‖))
                   = exp(4^{-n} · c · |Λ^{(n)}| · (1 + ‖f^{(n)}‖/|Λ^{(n)}|))
```
Using |Λ^{(n)}| ~ 4ⁿ|K| and ‖f^{(n)}‖_{L^p}^p = 4ⁿ‖f‖_{L^p}^p:
```
4^{-n} · c · 4ⁿ|K| · (1 + ‖f‖^p) = c(|K| + ‖f‖_{L^p}^p)
```
**The 4^{-n} exponent from reflection exactly cancels the 4^n growth of the support!**

### 22. Transfer to OS Axioms (Theorem 11.2.1 continued)

Once the infinite-volume limit S{f} exists:

**OS0 (Temperedness):** Follows from the regularity bound |S{f}| ≤ exp(c(‖f‖_{L¹} + ‖f‖_{L^p}^p)).

**OS2 (Euclidean invariance):** The finite-volume measures dμ_Λ are not exactly Euclidean invariant (they depend on Λ). But the limit is, because:
- Translation: S_Λ{T_a f} = S_{Λ-a}{f} → S{f} by uniqueness of limit
- Rotation: Similar argument using rotated volumes

**OS3 (Reflection positivity):** RP is preserved under limits. Since each dμ_Λ is RP (Theorem 10.4.3), the limit dμ is RP.

---

## Part VI: Regularity (Chapter 12, WP4)

### 23. Integration by Parts and Schwinger-Dyson Equations

**The Euclidean equation of motion (Corollary 12.2.3).** For f ∈ C₀^∞:
```
∫ φ(f) A(φ) dμ = ∫ ⟨Cf, δA/δφ⟩ dμ - λ∫ A(φ)⟨Cf, :φ³:⟩ dμ
```

**Proof.** Start with the Gaussian IBP formula:
```
∫ φ(f) A · e^{-V} dφ_C = ∫ ⟨Cf, δ(A e^{-V})/δφ⟩ dφ_C
```
Expand the functional derivative:
```
δ(A e^{-V})/δφ = (δA/δφ) e^{-V} + A · (-δV/δφ) e^{-V}
```
For V = λ∫:φ⁴:, δV/δφ = 4λ:φ³:. Dividing by Z:
```
∫ φ(f) A dμ = ∫ ⟨Cf, δA/δφ⟩ dμ - 4λ∫ A⟨Cf, :φ³:⟩ dμ
```

**Wick powers in infinite volume (Theorem 12.2.1).** :φ^j: = lim_{κ→∞} :φ_κ^j: exists in L²(dμ), and UV/IR limits commute. This extends Wick products from the free theory (where they're defined by Gaussian structure) to the interacting theory.

### 24. The Regularity Theorem (Theorem 12.5.1 / OS1)

**Statement.** For P = even polynomial + linear term, there exists c < ∞ such that for all f ∈ C₀^∞:
```
S{-if} = ∫ exp(φ(f)) dμ ≤ exp(c(‖f‖_{L¹} + ‖f‖_{L^{4/3}}^{4/3}))
```

This is the **regularity axiom OS1** — the generating functional grows at most exponentially in the L¹ and L^{4/3} norms of the test function.

**Proof outline (6 steps):**

*Step 1: Large/small decomposition.* Decompose f = g + h over unit squares Δ:
- g = Σ_{Δ "large"} f_Δ where "large" means ‖f_Δ‖_{L¹} + ‖f_Δ‖_{L^{4/3}}^{4/3} ≥ 1
- h = Σ_{Δ "small"} f_Δ

By Schwarz: ∫ e^{φ(f)} dμ ≤ (∫ e^{2φ(g)} dμ)^{1/2} (∫ e^{2φ(h)} dμ)^{1/2}.

*Step 2: Large part.* Use multiple reflections (Corollary 10.5.8) + the uniform bound (Theorem 12.4.1):
```
∫ e^{2φ(g)} dμ ≤ ∏_{Δ large} exp(c(1 + ‖g_Δ‖_{L^{4/3}}^{4/3}))
```
Number of large squares ≤ ‖f‖_{L¹} + ‖f‖_{L^{4/3}}^{4/3}. Done.

*Step 3: Small part setup.* For h with ‖h_Δ‖ small on each square, write:
```
e^{φ(h_Δ)} = 1 + F_Δ + G_Δ
```
where F_Δ = φ(h_Δ) (linear) and G_Δ = e^{φ(h_Δ)} - 1 - φ(h_Δ) (higher order).

*Step 4: Integration by parts on F factors.* Each factor φ(h_Δ) is contracted using the Schwinger-Dyson equation:
```
∫ φ(h_Δ) · B dμ = ∫ ⟨Ch_Δ, δB/δφ⟩ dμ - λ∫ B⟨Ch_Δ, :φ³:⟩ dμ
```

Three types of contractions:
- (i) **F-F:** ⟨h_i, C h_j⟩ ≤ const · e^{-m·dist(Δᵢ,Δⱼ)} [exponential decay]
- (ii) **F-G:** bounded by localized graph estimates
- (iii) **F-V:** produces :φ³: vertex, bounded by graph estimates

*Step 5: Exponential decay controls combinatorics.* The k-th contraction to square Δ has distance d_k satisfying k ≤ const · d_k² (geometric packing in 2D). Therefore:
```
∏_{k=1}^{n(Δ)} O(1) e^{-const√k} ≤ exp(const · n(Δ) - const · n(Δ)^{3/2})
```

The **superlinear convergence** (n^{3/2} vs n) dominates all combinatorial factors and ensures the infinite product converges.

*Step 6: Final bound.* Assembling all contractions:
```
∫ e^{φ(h)} dμ ≤ ∏_Δ (1 + 2c‖h_Δ‖) ≤ ∏_Δ exp(2c‖h_Δ‖) = exp(2c‖h‖_{L¹})
```

**Key mathematical insight:** The entire regularity proof rests on the **exponential decay of the massive propagator** C(x,y) ~ e^{-m|x-y|}. This provides spatial decorrelation that tames the combinatorial explosion from integration by parts.

### 25. Asymmetric Reflections and Volume Independence (Section 12.4)

**The problem:** Theorem 11.3.1 gives a bound that depends on |K| (support of f), but the infinite-volume regularity theorem needs a bound independent of |Λ| (the approximating volume).

**Theorem 12.4.1 (Volume-independent bound).** For any K containing supp(g):
```
∫ exp(:φ^j(g):) dμ_{Λ_ν} ≤ exp(c(|K| + ‖g‖_{L^p}^p))
```
along a subsequence Λ_ν → R².

**Proof strategy:** Use **asymmetric reflections** (Prop. 10.6.1) — reflections where the number of horizontal and vertical reflections can differ.

Choose Λ_ν to be oblong rectangles T × L with T ≫ L:
1. Perform j₀ vertical reflections and j₁ horizontal reflections (j₁ ≫ j₀)
2. After reflections: exponent picks up factor 2^{-(j₀+j₁)}
3. Vertical reflections: determinant factors ~ O(1)
4. Horizontal reflections: each costs exp(O(|K|)) but gains factor 2^{-1} in exponent
5. Partition function ratios: use spectral analysis Z(T,L) ~ e^{-TE_L} where E_L = inf spec(H_L)

The spectral analysis of the transfer matrix Hamiltonian H_L (the generator of translations in the T-direction) is the new ingredient beyond Chapter 11.

---

## Part VII: Synthesis — Complete OS Axioms and Reconstruction

### 26. OS Axioms Summary

| Axiom | What it says | Where proved | Key technique |
|-------|-------------|-------------|---------------|
| OS0 | Temperedness | Thm 11.2.1 | Uniform bound + analyticity |
| OS1 | Regularity | Thm 12.5.1 | IBP + exponential decay |
| OS2 | Euclidean invariance | Thm 11.2.1 | Limit of invariant approximations |
| OS3 | Reflection positivity | Thm 10.4.3 + limit | RP preserved under limits |
| OS4 | Clustering | Thm 18.1.1 | Cluster expansion (weak coupling) |

**Note:** OS4 requires **weak coupling** (λ/m⁶ small). The other axioms hold for all λ > 0.

### 27. Wightman Reconstruction

From OS0-OS4, the reconstruction theorem (Chapter 19) gives:

1. **Hilbert space** H with vacuum Ω and Hamiltonian H ≥ 0
2. **Field operators** Φ_M(f) essentially self-adjoint on H
3. **Lorentz covariance** from analytic continuation of Euclidean rotations
4. **Locality** from analytic continuation of Euclidean permutation symmetry
5. **Spectrum condition** |P| ≤ H from Lorentz covariance + H ≥ 0
6. **Unique vacuum** from clustering (OS4)

### 28. The Cluster Expansion (Chapter 18)

**Why it's needed:** The correlation inequalities (GKS, FKG) and multiple reflections give OS0-OS3 for all λ > 0, but OS4 (clustering) requires a different technique — the **cluster expansion** — which works only for λ small.

**Setup.** Introduce interpolation parameters s_b ∈ [0,1] for each bond b in a lattice tiling of Λ. The covariance C(s) interpolates between:
- s = 1: full covariance (coupled)
- s = 0: Dirichlet-decoupled covariance (independent squares)

**The expansion (Theorem 18.2.5):**
```
S_Λ(f) = Σ_{X, Γ} ∫ ∂^Γ [∏φ(x_i) e^{-λV(Λ∩X)} dφ_{C(s(Γ))}] ds(Γ) · Z_{∂X}/Z_Λ
```
where X ranges over connected subsets of the lattice, Γ ⊂ X indexes active bonds.

**Convergence (Theorem 18.3.1).** Three estimates:
1. **Combinatorial:** #{terms with |X| = k} ≤ e^{K₁k}
2. **Partition function ratios:** |Z_{∂X}/Z_Λ| ≤ e^{K₂|X|}
3. **Function space integral:** Each ∂/∂s_b costs O(m⁻ʳ) with exponential spatial decay

For λ/m⁶ ≪ 1, the decay beats the combinatorial growth, and the expansion converges absolutely.

**Clustering from convergence:** The expansion represents S_Λ(f₁,...,f_n) as a sum over connected sets X. For the truncated (connected) correlation function, X must connect all observation points. If the points are separated by distance d, then |X| ≥ d, giving:
```
|S_n^{connected}(x₁,...,x_n)| ≤ const · e^{-Kd}
```

**Note:** The cluster expansion is NOT perturbation theory in λ. It's an expansion in the spatial coupling structure (which bonds are active). Each term is computed non-perturbatively. The weak coupling condition ensures convergence but does not make the result perturbative.

---

## Appendix A: The Formalization Gap Structure

### Current Status (2026-03-28)

```
Theorem-level sorry:  21
Legacy Model classes: 13
Canonical gap_* frontiers: 45
Axioms: 0
```

### WP1 Critical Path (The Bottleneck)

Two independent branches, both required:

**Branch 1: Shell Estimates** (control UV convergence)
```
gap_wickPowerStandardSeqShellUpper_spatial_sq_rate (10) ← ROOT, sorry
  → gap_wickPower_standardSeq_spatial_sq_rate (11) [closed mod 10]
    → gap_interactionCutoff_standardSeq_L2_increment_rate (12) [closed mod 10]
      → gap_interactionCutoff_standardSeq_summable_L1_increments (13) [closed mod 12]
        → gap_interactionCutoff_standardSeq_ae_convergence (14) [closed mod 13]
```
Also:
```
gap_interactionCutoff_L2_convergence (15) ← sorry
gap_interactionCutoff_ae_convergence (16) ← sorry
```

**Branch 2: Nelson Bound** (control double-exponential tail)
```
gap_uvMollifier_freeCovKernel_log_growth ← ROOT, sorry (in FreeField.lean)
  → gap_regularizedPointCovariance_log_growth (19) [closed mod above]

gap_centeredGaussian_mvPolynomial_even_moment_comparison ← ROOT, sorry (in WickProduct.lean)
  → gap_finiteWickCylinder_even_moment_comparison (22) [closed mod above]
    → gap_interactionCutoffSubUniformApprox_even_moment_comparison (23) [closed mod 22]
      → gap_interactionCutoff_sub_even_moment_comparison (24) [closed mod 23]

gap_interactionCutoff_reference_shell_L2_bound (25) ← sorry
  + gap_interactionCutoff_sub_even_moment_comparison (24)
    → gap_interactionCutoff_reference_shell_even_moment_bound (26) [closed mod 24,25]
      → gap_interaction_double_exponential_tail_bound (27) [closed mod 19,24,25]
        → gap_exp_neg_interaction_uniform_bound (28) [closed mod 27]
```

**Endpoint:** gap_hasExpInteractionLp (29) [closed mod all above]

### Root Gaps (True Leaves)

The actual mathematical work needed reduces to these **root sorry's**:

1. **gap_uvMollifier_freeCovKernel_log_growth** (FreeField.lean): Prove c_κ ≤ C₀ + K ln κ at the kernel level
2. **gap_uvMollifier_covariance_eq_freeCovKernel** (FreeField.lean): Match CLM covariance to kernel covariance for mollifiers
3. **gap_covariance_eq_kernel** (FreeField.lean): Full CLM ↔ kernel identification
4. **gap_wickPowerStandardSeqShellUpper_spatial_sq_rate** (ShellEstimates.lean): Shell-side spatial square rate
5. **gap_centeredGaussian_mvPolynomial_even_moment_comparison** (WickProduct.lean): Finite-dimensional hypercontractivity
6. **gap_interactionCutoff_reference_shell_L2_bound** (NelsonBound.lean): Reference shell L² bound
7. **gap_interactionCutoff_L2_convergence** (ShellEstimates.lean): Continuous-parameter L² convergence
8. **gap_interactionCutoff_ae_convergence** (ShellEstimates.lean): Continuous-parameter a.e. convergence

---

## Appendix B: Key Estimates Reference Card

| Estimate | Statement | Where used | GJ Reference |
|----------|-----------|-----------|--------------|
| Semiboundedness | :φ⁴: ≥ -6c_κ² | WP1 Step 1 | Prop 8.6.3 |
| Small bad set | μ(χ(κ)) ≤ e^{-ακ^ε} | WP1 Step 2 | Prop 8.6.4 |
| Localized graph bound | |I(G)| ≤ ∏N(Δ)!(c/m)^{N(Δ)} | WP1, WP4 | Thm 8.5.5 |
| Log divergence | c_κ ≤ C₀ + K ln κ | WP1 (Nelson) | Sec 8.3 |
| Hypercontractivity | ‖P_t‖_{p→q} ≤ 1 | WP1 (Nelson) | Simon-HK 1972 |
| GKS-II | ⟨AB⟩ - ⟨A⟩⟨B⟩ ≥ 0 | WP3 (monotonicity) | Thm 4.1.3 |
| Chessboard | |∫∏k_α|≤∏L(k_α) | WP3 (uniform bound) | Cor 10.5.8 |
| Uniform bound | |S_Λ{f}| ≤ e^{c(|K|+‖f‖^p)} | WP3 | Thm 11.3.1 |
| IBP/Schwinger-Dyson | ∫φ(f)A dμ = ∫⟨Cf,δA/δφ⟩dμ - ... | WP4 | Cor 12.2.3 |
| Exponential decay of C | C(x,y) ~ e^{-m|x-y|} | WP3, WP4 | Prop 7.2.1 |
| Cluster expansion convergence | λ/m⁶ ≪ 1 | WP5 (OS4) | Thm 18.3.1 |

---

**Last updated:** 2026-03-28 14:55 UTC
