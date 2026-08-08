# CoRN/Rocq assumptions audit for Semeria's Bishop--Cheng DCT declarations

This directory contains a small reproducibility package for the independently
reproduced Rocq assumptions audit of Vincent Séméria's Bishop--Cheng dominated
convergence development in CoRN.

## Audited source

- Repository: <https://github.com/rocq-community/corn>
- CoRN commit: `ada7c0b497ff15dd67cf7932c6f20e143a2aee2f`
- Rocq version: `9.0.1`
- Source module: `reals/stdlib/CMTMeasurableFunctions.v`
- Audit file: `CoRNAxiomAudit.v`

The audited declarations are:

- `CvMeasure`
- `DominatedMeasureCvZero`
- `DominatedConvergence`

## Result

At CoRN commit `ada7c0b497ff15dd67cf7932c6f20e143a2aee2f`, using Rocq 9.0.1,
`Print Assumptions` reported `CvMeasure`, `DominatedMeasureCvZero`, and
`DominatedConvergence` as `Closed under the global context`.

The raw log is `corn-print-assumptions.log`. Its relevant result lines are:

```text
=== CvMeasure ===
Closed under the global context
=== DominatedMeasureCvZero ===
Closed under the global context
=== DominatedConvergence ===
Closed under the global context
```

## Interpretation

In other words, `Print Assumptions` listed no global axioms in the dependency
closure of these declarations. This is a statement about their global axiom
footprint, not an assertion that the theorems are free of mathematical
hypotheses: their statements remain parameterized by the explicitly quantified
`IntegrationSpace` and `ConstructiveReals` structures, whose fields specify the
mathematical setting in which the results are proved.

This package does not compare CoRN and Lean by saying that either development is
"more constructive" than the other. The CoRN result and the Lean result use
different real-number and integration-space interfaces, and their public theorem
surfaces are not ordered solely by logical strength.

## Reproduction

Run from this directory:

```bash
./commands.sh
```

The script clones CoRN, checks out the pinned commit, uses the pinned
`rocq/rocq-prover` Docker image digest recorded in `environment.txt`, builds the
required CoRN target, and reruns `CoRNAxiomAudit.v`.
