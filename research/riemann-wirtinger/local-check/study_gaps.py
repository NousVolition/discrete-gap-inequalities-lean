"""Evaluate the registered zeta-zero gap diagnostic; keep it separate from Lean proofs."""
from pathlib import Path
import csv, hashlib, json, sys, time
import mpmath as mp

ROOT = Path(__file__).resolve().parent
protocol_file = ROOT / "gap-study-protocol.json"
protocol = json.loads(protocol_file.read_text())
protocol_hash = hashlib.sha256(protocol_file.read_bytes()).hexdigest()
fmt = lambda value: mp.nstr(value, mp.mp.dps)

def run_pass(spec):
    mp.mp.dps = spec["decimal_precision"]
    roots = {n: mp.im(mp.zetazero(n)) for n in protocol["zero_indices"]}
    residuals = {n: abs(mp.zeta(mp.mpf("0.5") + mp.j * t)) for n, t in roots.items()}
    rows = []
    for left, right in protocol["pairs"]:
        a, b = roots[left], roots[right]
        grid = [a + (b-a)*j/spec["subintervals"] for j in range(spec["subintervals"]+1)]
        energy = mp.quad(lambda t: abs(mp.zeta(mp.mpf("0.5") + mp.j*t))**2,
                         grid, method="gauss-legendre")
        derivative_energy = mp.quad(lambda t: abs(mp.zeta(mp.mpf("0.5") + mp.j*t, derivative=1))**2,
                                    grid, method="gauss-legendre")
        gap = b-a
        lower = mp.pi * mp.sqrt(energy / derivative_energy)
        rhs = (gap/mp.pi)**2 * derivative_energy
        rows.append({"pair": [left, right], "left_zero": fmt(a), "right_zero": fmt(b),
                     "gap": fmt(gap), "energy": fmt(energy), "derivative_energy": fmt(derivative_energy),
                     "lower_bound": fmt(lower), "bound_fraction": fmt(lower/gap),
                     "inequality_slack": fmt(rhs-energy), "normalized_slack": fmt((rhs-energy)/rhs)})
        print(f"precision={mp.mp.dps} pair={left}-{right}: gap={float(gap):.8f}, bound={float(lower):.8f}", flush=True)
    return {**spec, "zeros": {str(n): fmt(t) for n,t in roots.items()},
            "endpoint_residuals": {str(n): fmt(r) for n,r in residuals.items()}, "rows": rows}

def main():
    started = time.monotonic()
    passes = [run_pass(spec) for spec in protocol["passes"]]
    assert protocol_hash == hashlib.sha256(protocol_file.read_bytes()).hexdigest()
    mp.mp.dps = 60
    keys = ["gap", "energy", "derivative_energy", "lower_bound", "bound_fraction", "inequality_slack"]
    discrepancies = []
    for a,b in zip(passes[0]["rows"], passes[1]["rows"], strict=True):
        for key in keys:
            x,y = mp.mpf(a[key]),mp.mpf(b[key])
            discrepancies.append({"pair": a["pair"], "quantity": key,
                                  "relative_difference": fmt(abs(x-y)/max(abs(y),mp.mpf("1e-50")))})
    agreement = max(mp.mpf(d["relative_difference"]) for d in discrepancies)
    residual_ok = all(mp.mpf(r) < mp.mpf(protocol["endpoint_residual_limits"][str(p["decimal_precision"])])
                      for p in passes for r in p["endpoint_residuals"].values())
    positive_slack = all(mp.mpf(row["inequality_slack"]) > 0 for p in passes for row in p["rows"])
    checks = {"relative_agreement": agreement < mp.mpf(protocol["relative_agreement_limit"]),
              "endpoint_residuals": residual_ok, "positive_slack": positive_slack}
    report = {"protocol_file": protocol_file.name, "protocol_sha256": protocol_hash,
              "script_file": Path(__file__).name, "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "mpmath_version": mp.__version__, "passes": passes, "comparisons": discrepancies,
              "maximum_relative_difference": fmt(agreement), "checks": checks,
              "numerical_status": "PASS" if all(checks.values()) else "FAIL",
              "elapsed_seconds": round(time.monotonic()-started,3), "scope": protocol["scope"]}
    (ROOT/"gap-study-results.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    with (ROOT/"gap-study-results.csv").open("w",newline="",encoding="utf-8") as f:
        writer=csv.DictWriter(f,fieldnames=list(passes[1]["rows"][0]))
        writer.writeheader(); writer.writerows(passes[1]["rows"])
    print(json.dumps({"status":report["numerical_status"],"checks":checks,
                      "maximum_relative_difference":report["maximum_relative_difference"]}),flush=True)
    return 0 if all(checks.values()) else 1

if __name__ == "__main__":
    sys.exit(main())
