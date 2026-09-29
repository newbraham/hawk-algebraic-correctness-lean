# HAWK Algebraic Correctness in Lean

Lean 4 formalization of the algebraic correctness layer underlying HAWK. The development separates a signing argument for arbitrary rank and positive integer modulus from the cyclotomic facts used to interpret the public quadratic form as a coefficient-Euclidean norm. HAWK is recovered at modulus two; an exact divisibility criterion describes when sign reversal also preserves integrality.

## Structure

- `Hawk/CyclotomicTrace.lean` proves the normalized cyclotomic trace/coefficient inner-product identity for the power-of-two cyclotomic field.
- `Hawk/Signing.lean` proves exact division, subring integrality, reconstruction, and Gram transport for every positive integer modulus in arbitrary module rank. It characterizes integrality after sign reversal and derives the HAWK theorems at modulus two.
- `Hawk/CyclotomicSigning.lean` combines the generic signing results with the cyclotomic trace identity.
- `Hawk/Examples.lean` contains eight exact rational sanity checks and a modulus-three counterexample showing that preservation of the metric does not imply integrality of the sign-flipped candidate.
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

## Signing correctness for arbitrary rank and modulus

For a positive integer $m$, $B\in\mathrm{GL}_r(R)$, $Q=B^\star B$, $h\in R^r$, and $x\in Bh+mR^r$, define

$$
w=B^{-1}x,\qquad s_m=\frac{h-w}{m}.
$$

Given a coset witness $x=Bh+mz$ with $z\in R^r$, the signature is $s_m=-B^{-1}z\in R^r$. Thus division is exact even when $m$ is not invertible in $R$. Reconstruction gives $h-ms_m=w$, applying $B$ gives $x$, and the public Gram form transports to the sampled vector.

The central matrix identity is established before applying the field trace:

$$
v^\star(B^\star B)v=(Bv)^\star(Bv).
$$

Main declarations:

```lean
Hawk.signature_integral_mod
Hawk.exact_division_mod
Hawk.reconstruction_mod
Hawk.gram_identity
Hawk.signing_correctness_mod
```

For the opposite preimage, put $s_m^-=(h+w)/m$. Under the same coset and inverse-integrality assumptions,

$$
s_m^-\in R^r\quad\Longleftrightarrow\quad 2h\in mR^r.
$$

The public metric is preserved for either sign regardless of this condition. At $m=2$, the condition holds for every integral $h$, and $s_2^-=h-s_2$. The original HAWK correctness declarations invoke the general theorems at this modulus.

At $m=3$, take $R=\mathbb Z\subseteq\mathbb Q$, rank one, $B=1$, and $h=x=1$. All basis and coset assumptions hold, but $s_3=0$ while $s_3^-=2/3\notin\mathbb Z$. The counterexample uses the actual image of the integer cast into the rationals and checks the metric equality as well as nonintegrality.

Sign criterion, counterexample, and HAWK specializations:

```lean
Hawk.flipped_signature_integral_iff
Hawk.signing_correctness_sign_mod
Hawk.Examples.modulus_three_counterexample
Hawk.signature_integral
Hawk.exact_half_unique
Hawk.signing_correctness
Hawk.signing_correctness_sign
Hawk.signing_correctness_over_ring
Hawk.verification_bound
```

## Cyclotomic composition

For every positive modulus, if the coordinates of the sampled vector have power-basis coefficients $a_{i,j}$, the cyclotomic specialization identifies the public quadratic form evaluated at $h-ms_m$ with

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
Hawk.CyclotomicSigning.signing_correctness_mod_coeff_norm
Hawk.CyclotomicSigning.signing_correctness_sign_mod_coeff_norm
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

The formalization covers the algebraic reconstruction and metric-transport layer. Hashing, Gaussian sampling, compression/decompression, encoding checks, restart behavior, correctness-failure probabilities, and security reductions are outside its scope. The development also does not prove that the chosen coefficient subring is the full ring of integers. Generalizing the modulus demonstrates reuse of these algebraic proofs; it does not define or establish the security of another signature scheme.
