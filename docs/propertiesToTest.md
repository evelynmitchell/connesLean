# Operator Properties to Test

Base operator properties for the restricted Weil quadratic form E_lambda
and its associated self-adjoint generator H_lambda on L²(I).

## Core properties

1. Symmetric, densely defined quadratic form E_lambda on L²(I)
2. Closed (lower semicontinuous) form
3. Semibounded / nonnegative form
4. Markov (Dirichlet form; normal contraction property)
5. Beurling-Deny pure-jump structure (difference-energy / jump form)
6. Selfadjoint generator H_lambda (Friedrichs/Kato representation)
7. Sub-Markovian / positivity-preserving semigroup e^{-tH}
8. Irreducibility (no nontrivial invariant closed ideals)
9. Positivity improving semigroup (for t > 0)
10. Compact resolvent
11. Discrete spectrum (pure point; finite multiplicities; only accumulation at +infinity)
12. Existence of ground-state eigenvalue lambda_0
13. Ground state strictly positive a.e.
14. Ground state eigenvalue simple
15. Reflection symmetry (commutes with parity operator)
16. Even/odd invariant subspace decomposition
17. Ground state even
18. Spectral gap above ground state (strict inequality lambda_1 > lambda_0)
19. Variational/min-max characterization of eigenvalues
20. Rayleigh-Ritz/Galerkin upper bounds; monotone convergence with form-dense subspaces
21. Stability under bounded perturbations (selfadjointness and compact resolvent preserved)
22. Finite-rank perturbation determinant/Birman-Schwinger characterization (when applicable)
23. Whole-line translation-invariant extension with explicit Levy symbol psi(xi)
24. Fourier-multiplier representation on L²(R) (Levy-Khintchine form)
25. Spectral zeta function and regularized determinant/canonical product (existence)

## Ordered by importance for proving even / simple ground state

Tagging hard items:

1. Parity symmetry; even/odd block decomposition
2. Finite-rank pole term; rank-two -> two rank-one updates after parity diagonalization
3. Birman-Schwinger / Weinstein-Aronszajn scalar/determinant characterization
4. Positivity improving semigroup for the base operator (Perron-Frobenius leverage) **hard**
5. Base ground state strictly positive a.e. **hard**
6. Base ground state eigenvalue simple **hard**
7. Irreducibility (enables positivity improving in the killed setting) **hard**
8. Markov/Dirichlet-form property (enables the positive semigroup framework) **hard**
9. Compact resolvent (discrete spectrum; needed for PF + eigen-expansions)
10. Resolvent domination/comparison (killed interval vs whole-line)
11. Whole-line translation-invariant extension with explicit symbol psi(xi)
12. Archimedean log-growth coercivity bound for psi(xi)
13. Variational/min-max principle
14. Rayleigh-Ritz/Galerkin monotone upper bounds (parity-separated)
15. Stability of compact resolvent under bounded perturbations
