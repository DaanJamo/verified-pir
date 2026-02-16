[![DOI](https://zenodo.org/badge/932826354.svg)](https://doi.org/10.5281/zenodo.18657494)

# A Verified Extraction for PIR

This project aims to provide an end-to-end certified pipeline from Rocq
to Plutus Core, by defining a verified translation from [LambdaBox-Typed](https://github.com/AU-COBRA/ConCert) to [Plutus Intermediate Language](https://plutus.cardano.intersectmbo.org/docs/essential-concepts/plinth-and-plutus-core).
This translation bridges the gap between [MetaRocq's verified erasure](https://github.com/MetaRocq/metarocq?tab=readme-ov-file#erasure) procedure and the [Plutus-Cert translation certifier](https://github.com/basetunnel/plutus-cert). Currently, it supports a subset of $\lambda_\square^T$ consisting of the simply-typed $\lambda$-calculus with global definitions.

The main files are [Translation.v](https://github.com/DaanJamo/verified-pir/blob/main/theories/Translation.v) which defines the translation as a function and a logical relation, [Semantics.v](https://github.com/DaanJamo/verified-pir/blob/main/theories/Semantics.v) which contains proofs to show that our translation preserves the evluation semantics of programs within our supported subset, and [Pipeline.v](https://github.com/DaanJamo/verified-pir/blob/main/theories/Pipeline.v) which defines a (not yet verified) end-to-end extraction procedure from Rocq to PIR.

## Setup & Usage

First run `nix develop`, `code .`, then insert the path from `which coq-lsp` into the coq-lsp vscode plugin settings.

Now import `MetaCoq.Template.Loader` and either `Pipeline.v` (for `compile_pir` or `compile_and_print_pir`) or `PrettyPipeline.v` (for `show_pir_pipeline`) 
in a Rocq file together with the definition you want to extract. Then run `Eval vm_compute in {function} <# {definition name} #>.` 
to extract the definition to PIR (if it falls within the supported subset).

## [Simple](https://github.com/DaanJamo/verified-pir/tree/main/theories/Simple)

This folder contains experiments done to get familiar with the main semantics preservation proof. 
- [NamedToPIR.v](https://github.com/DaanJamo/verified-pir/blob/main/theories/Simple/NamedToPIR.v) defines a trivial verified translation from a named STLC to PIR, which also uses a named representation.
- [DBToPIR.v](https://github.com/DaanJamo/verified-pir/blob/main/theories/Simple/DBToPIR.v) defines a verified translation between a STLC that uses De Bruijn indices and the named PIR, 
similar to the main proof but without e.g. type annotations.
- [SimplePipeline](https://github.com/DaanJamo/verified-pir/blob/main/theories/Simple/SimplePipeline.v) defines an unverified pipeline from Gallina to PIR via DB. [EAstToDB.v](https://github.com/DaanJamo/verified-pir/blob/main/theories/Simple/EAstToDB.v) translates $\lambda_{\square}$ to *DB*, hallucinating types as needed.

## Publication
Link to Thesis TBA
