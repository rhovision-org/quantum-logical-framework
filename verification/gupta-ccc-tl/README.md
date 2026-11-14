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

## Executed result

| Observed redshift | Computed age (Gyr) | Published target (Gyr) | Absolute difference (Gyr) |
|---|---|---|---|
| 0 | 26.667211859 | 26.7 | 0.032788141 |
| 10 | 5.832453379 | 5.8 | 0.032453379 |
| 20 | 3.463280173 | 3.5 | 0.036719827 |

All three targets pass the frozen 0.05 Gyr tolerance. At the published rounded inputs the present age is 26.6672 Gyr, so Table 1's additional hundredth (26.70) is not recovered at that precision. The abstract-precision benchmark passes; the extra-precision discrepancy remains for independent review. This result does not constrain the open QLF age map.

Validation: seven reference tests pass, including the original evolution equation, independent age quadrature, low-redshift total slope, external Hc scale sensitivity and a deliberately wrong target that must fail. The typed-record validator and document-link checker pass. Existing document-to-Lean back-link warnings for Manifestation and Maxwell are outside this change.
