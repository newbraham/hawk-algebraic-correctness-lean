# HAWK Algebraic Correctness in Lean

Lean 4 formalization of the algebraic correctness layer underlying HAWK. The development separates the generic signing argument from the cyclotomic facts used to interpret the public quadratic form as a coefficient-Euclidean norm.

## Structure

- `Hawk/CyclotomicTrace.lean` proves the normalized cyclotomic trace/coefficient inner-product identity for the power-of-two cyclotomic field.
- `Hawk/Signing.lean` proves exact division by two, subring integrality, reconstruction, Gram transport, the sign-symmetry branch, and verification-bound transfer in arbitrary module rank.
- `Hawk/CyclotomicSigning.lean` combines the generic signing results with the cyclotomic trace identity.
- `Hawk/Examples.lean` contains small exact sanity checks.
- `Audit.lean` checks the axiom dependencies of the declarations in the `Hawk` namespace.

## Toolchain

The project targets Lean **4.19.0**. The dependency versions are pinned by `lake-manifest.json`.

## Build

Install Lean through `elan`, then run:

```sh
lake exe cache get
lake --wfail build
lake env lean -DwarningAsError=true Audit.lean
```

The GitHub Actions workflow runs the same build and audit checks.

## Cyclotomic coefficient geometry

Let

$$
n=2^k,\qquad E=\mathbb{Q}(\zeta_{2n}).
$$

For the power basis $1,\zeta,\ldots,\zeta^{n-1}$, the formalization proves

$$
\frac{1}{n}\mathrm{Tr}_{E/\mathbb{Q}}(a^\star b)
=\sum_{i=0}^{n-1} a_i b_i,
$$

and, in particular,

$$
\frac{1}{n}\mathrm{Tr}_{E/\mathbb{Q}}(a^\star a)
=\sum_{i=0}^{n-1} a_i^2.
$$

The proof derives trace orthogonality from Mathlib's cyclotomic-extension interface. It reindexes embeddings by primitive roots, enumerates those roots by odd powers of the canonical primitive root, evaluates the resulting geometric sums, and constructs the automorphism sending $\zeta$ to $\zeta^{-1}$.

Main declarations:

```lean
Hawk.CyclotomicTrace.traceOrthogonality_hawk
Hawk.CyclotomicTrace.cyclotomic_trace_coeff_inner
Hawk.CyclotomicTrace.cyclotomic_trace_coeff_sq
```

`TraceOrthogonality` is used as an intermediate predicate; the concrete endpoint theorems discharge it.

## Rank-generic signing correctness

For $B\in\mathrm{GL}_r(R)$, $Q=B^\star B$, $h\in R^r$, and $x\in Bh+2R^r$, define

$$
w=B^{-1}x,\qquad s=\frac{h-w}{2}.
$$

The generic layer proves that $s$ lies in the coefficient ring, reconstruction returns $w$, applying $B$ returns $x$, and the public Gram form transports to the sampled vector. It also proves the sign-symmetry branch $w'=-w$, $s'=h-s$ and the corresponding verification-bound transfer.

The central matrix identity is established before applying the field trace:

$$
v^\star(B^\star B)v=(Bv)^\star(Bv).
$$

Main declarations:

```lean
Hawk.signature_integral
Hawk.exact_half_unique
Hawk.gram_identity
Hawk.signing_correctness
Hawk.signing_correctness_sign
Hawk.signing_correctness_over_ring
Hawk.verification_bound
```

## Cyclotomic composition

If the coordinates of the sampled vector have power-basis coefficients $a_{i,j}$, the cyclotomic specialization identifies the public quadratic form with

$$
\sum_i\sum_j a_{i,j}^2,
$$

and its associated square-root expression with

$$
\sqrt{\sum_i\sum_j a_{i,j}^2}.
$$

Main declarations:

```lean
Hawk.CyclotomicSigning.cyclotomicConjugation_involutive
Hawk.CyclotomicSigning.cyclotomicTraceSq_coeffVector
Hawk.CyclotomicSigning.signing_correctness_coeff_norm
Hawk.CyclotomicSigning.signing_correctness_sign_coeff_norm
```

## Audit

`Audit.lean` checks the user-facing declarations in the `Hawk` namespace and accepts only the standard foundational dependencies

```text
propext
Classical.choice
Quot.sound
```

The CI audit also fails if `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler` appears in the audit output.

## Scope

The formalization covers the algebraic reconstruction and metric-transport layer. Hashing, Gaussian sampling, compression/decompression, encoding checks, restart behavior, correctness-failure probabilities, and security reductions are outside its scope. The development also does not prove that the chosen coefficient subring is the full ring of integers.
