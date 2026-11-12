# Strange-loop observer toy — verification

**Status:** reproducible toy model / underdetermination demonstration. **Not** QLF evidence, not a detector model, not a physical probability derivation.

**Code:** [`tools/strange_loop_observer.py`](../../tools/strange_loop_observer.py)  
**Output:** [`strange_loop_observer.json`](strange_loop_observer.json)  
**Output SHA-256:** `0a703861b139740614e2d49c37d497277b0216da4a9bcabee801ab465e3cf74e`  
**Tests:** [`tests/test_strange_loop_observer.py`](../../tests/test_strange_loop_observer.py)

## What it asks

Paper I v0.3 leaves the optical, α, SPARC and Born bridges `B-OPEN`. The strange-loop reading asks what finite record a claimed loop returns to. This toy asks the narrow optical question:

> Does a pure MO2 closure walk reproduce the three-polarizer `1/8`, or does the operational re-preparation/probability map do the work?

## Run

```bash
python3 tools/strange_loop_observer.py
python3 tools/strange_loop_observer.py --json verification/strange-loop/strange_loop_observer.json
python3 -m unittest discover -s tests -p 'test_strange_loop_observer.py' -v
```

## Result

| Model | Transmission | Interpretation |
|---|---:|---|
| Operational Malus comparator | **0.125** | the conventional ideal-optics `1/8` |
| Pure MO2 meet walk | **0.0** | blocked at stage 2: `inf(az, ax) = bot` |
| Re-preparation, uniform weights | **0.125** | matches `1/8`, but the uniform weights are an extra assumption |
| Re-preparation, biased weights `0.6` | **0.216** | same lattice pass/block pattern, different transmission |
| Blanket integrating first two stages only | **0.25** | the third stage is outside the observer's blanket |
| Self-screen fixed point | **true** | toy idempotence only; not a physical bridge |

**Conclusion:** the pure MO2 meet does **not** produce `1/8`; it produces `0`. A re-preparation walk produces `1/8` only under uniform or Malus-supplied weights, and different weights with the same lattice pattern produce different transmissions. The lattice alone is underdetermined; the operational map is the missing premise. That is why `claim_records/three_polarizer.json` keeps `bridge: OPEN` and `strange_loop.status: B-OPEN`.

## Scope

- Finite toy; exact arithmetic/rounding only.
- No detector, angle calibration, optical data, or physical probability law is modeled.
- The "self-reference" is a state used as its own screen; its fixed point is mathematically trivial and is not a physical claim.
- The model does not show that QLF "fails" or "succeeds"; it localizes the missing operational premise.

See [`Strange_Loops.md`](../../Strange_Loops.md) §4–§6 and [`Claim_Status.md`](../../Claim_Status.md).
