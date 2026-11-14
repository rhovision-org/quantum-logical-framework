# Gupta reference execution record

[Program](../../Gupta_CCC_TL.md) · [Specification](specification.json) · [Numerical report](result.json)

The specification-only commit is `7368d89996db38165deb949961082ad83b3b3c2f`; its targets were already public and known. This is a self-run retrospective reproduction. Independent numerical review is pending. No F, E, or QLF bridge promotion is claimed.

The source download endpoint `https://arxiv.org/src/2309.13100v1` returned the article PDF; the received-byte SHA-256 is recorded in the specification. Equations were checked against the arXiv PDF, including the past cubic branch, the expansion/TL distance match and equation 50. The downloaded source is scratch material, not redistributed here.

`result.json` records the executed Git revision and the specification/implementation digests. `SHA256SUMS` covers the implementation, frozen specification, tests and result. Run from the repository root:

```bash
python3 tools/gupta_ccc_tl_reference.py
sha256sum -c verification/gupta-ccc-tl/SHA256SUMS
```

The 2048/4096-panel comparison estimates numerical stability; it is not a rigorous error bound or a parameter uncertainty. Independent age quadrature and finite-difference checks of the original evolution equation check the analytic solution. The listed ages use rounded published fitted inputs. Parameter covariance, alternative source versions, observational likelihoods and an empirical model comparison remain outside this execution.
