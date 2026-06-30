# Numerical validation campaign

Self-contained, targeted simulations that numerically witness each claim the Lean side states or
proves. Each experiment isolates one theorem or proposition, runs from a fixed seed, and prints an
explicit PASS or FAIL against a numeric criterion. Each is committed as a `science`-profile CKC
claim linked to the math claim it tests.

| Experiment | Tests | Criterion |
| --- | --- | --- |
| E1 mass transport | Lemma B.2 / B.1 | mass fraction in `B0 cap B1 >= 1-eps`; chain gives `>= (1-eps)^K` |
| E2 clustering | Proposition 2.1 | `diam(conv_g supp mu(t)) -> 0`, rate ~ `log(1/eps)` |
| E3 disentanglement | Proposition 3.1 | supports become pairwise disjoint; switches ~ `O(dN)` |
| E4 matching | Proposition 4.2 / 4.1 | `x_0^M -> y^M`, inactive points fixed; switches `<= 6M` |
| E5 Lyapunov | Example 6.1 | `E = 1 - cos theta` decreases; `x_i -> u_i` |
| E6 end-to-end | Theorems 1.1 / 1.2 | `W2(mu(T), target) <= eps`; switch count `O((d+M)N)` |
| E7 linear impossibility | eq. 1.7 | a single linear continuity equation cannot match overlapping -> disjoint |

## Run

```
uv run python -m E1_mass_transport.run
```

Outputs (figures, manifest, summary) land under `results/`.
