"""Closed packet, claims, record cross-checks, article consistency and privacy (no SAT or Lean run).

Usage: python3 -B check_packet.py      (ci_check.py and recheck_certificates.py re-run computations)
"""
import ast
import collections
import gzip
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
VERSION = "1.0.0"
REPOSITORY = "https://github.com/tkmt-lab/heesch-certificates"
PAPER = "paper-heesch-certificates-v2.1-en"
THEOREMS = ["Heesch.hh_sound_square", "Heesch.hc_sound_square", "Heesch.hh_sound_hex", "Heesch.hc_sound_hex",
            "Heesch.hh_sound_tri", "Heesch.hc_sound_tri"]
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
GRID = {"omino": "square", "hex": "hexagonal", "iamond": "triangular"}


def sha(p):
    h = hashlib.sha256()
    with Path(p).open("rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def load(name):
    return json.loads((ROOT / name).read_text())


def jsonl(path):
    raw = (ROOT / path).read_bytes()
    if str(path).endswith(".gz"):
        raw = gzip.decompress(raw)
    return [json.loads(l) for l in raw.decode().splitlines()]


def tree():
    return [p for p in ROOT.rglob("*") if p.relative_to(ROOT).parts[0] not in (".git",)
            and not (p.relative_to(ROOT).parts[:2] == ("formal", ".lake"))
            and not (p.relative_to(ROOT).parts[:2] == ("tools", "drat-trim"))]


def fp(r):
    p = Path(r["path"])
    assert not p.is_absolute() and ".." not in p.parts, p
    q = ROOT / p
    assert q.is_file() and sha(q) == r["sha256"] and q.stat().st_size == r["bytes"], ("fingerprint", str(p))


def main():
    # 1. closed inventory (formal/.lake and tools/drat-trim are build outputs, ignored by git)
    rows = {}
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        assert name not in rows
        rows[name] = digest
        assert sha(ROOT / name) == digest, ("inventory hash", name)
    actual = {p.relative_to(ROOT).as_posix() for p in tree() if p.is_file()}
    assert actual == set(rows) | {"SHA256SUMS"}, sorted(actual ^ (set(rows) | {"SHA256SUMS"}))
    assert not any(p.is_symlink() for p in tree())
    assert not any("__pycache__" in p.parts or p.suffix in (".pyc", ".log", ".aux") for p in tree())
    for p in tree():
        if p.suffix == ".py":
            ast.parse(p.read_text(), filename=p.name)
    prov = load("PROVENANCE.json")
    assert prov["version"] == VERSION and prov["uploaded"] is False and prov["release_assets"] == []
    assert {r["path"] for r in prov["files"]} == actual - {"SHA256SUMS", "PROVENANCE.json"}
    for r in prov["files"]:
        fp(r)
    for r in load("source-derivatives.json")["records"]:
        fp(r["public"])

    # 2. claims
    claims = load("claims.json")
    assert claims["version"] == VERSION
    fp(claims["paper"])
    fp(claims["pdf"])
    assert claims["scope"] == dict(human_expert_review=False, lean_internal_unsat_proofs=False,
                                   lrat_or_verified_checker=False, off_grid_placements=False,
                                   exhaustive_beyond_listed_inputs=False, counting_formally_verified=False,
                                   inputs_redistributed=False, priority_claimed=False), "unsupported scope promotion"
    kinds = set(claims["kinds"])
    assert kinds == {"lean-proof", "finite-computation", "independent-implementation", "prose"}
    by_id = {}
    for c in claims["claims"]:
        assert c["kind"] in kinds and c["evidence"] and c["id"] not in by_id
        by_id[c["id"]] = c
        for r in c["evidence"]:
            fp(r)
        if c["kind"] == "lean-proof":
            assert c["lean"]["axioms"] == AXIOMS
        else:
            assert "lean" not in c
    assert by_id["encoding-soundness"]["lean"]["declarations"] == THEOREMS
    assert by_id["square-instance-equals-earlier-definition"]["lean"]["declarations"] == ["HeeschProof.cnfOrd_square"]
    assert by_id["values-agree-second-encoding"]["kind"] == "independent-implementation"
    assert "no proof certificate" in by_id["maximal-corona-counts"]["qualification"]
    assert "not exhaustive" in by_id["restricted-search"]["qualification"]
    assert claims["not_claimed"] and "human expert review" in claims["not_claimed"]

    # 3. Lean files
    cmp = load("formal/comparator.json")
    assert cmp["theorem_names"] == THEOREMS and sorted(cmp["permitted_axioms"]) == sorted(AXIOMS)
    assert cmp["challenge_module"] == "Heesch.Challenge" and cmp["solution_module"] == "Heesch.Solution"
    axioms_file = (ROOT / "ci/Axioms.lean").read_text()
    assert all(f"#print axioms {t}\n" in axioms_file for t in THEOREMS + ["HeeschProof.cnfOrd_square"])
    challenge = (ROOT / "formal/Heesch/Challenge.lean").read_text()
    assert challenge.count(":= by sorry") + challenge.count(":= sorry") + len(re.findall(r"\n\s+sorry\b", challenge)) == 6
    assert re.findall(r"^import (.*)$", challenge, re.M) == ["Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected",
                                                               "Mathlib.Data.Set.Finite.Basic"]
    for p in (ROOT / "formal").rglob("*.lean"):
        t = re.sub(r"/-.*?-/|--[^\n]*", "", p.read_text(), flags=re.S)
        assert "native_decide" not in t and not re.search(r"^\s*axiom\s", t, re.M), p
        if p.name != "Challenge.lean":
            assert not re.search(r"\bsorry\b", t), p
    for t in THEOREMS:
        assert f"theorem {t.split('.')[1]}" in challenge
    log = (ROOT / "evidence/comparator-public-names-2026-10-23.txt").read_text()
    assert log.rstrip().endswith("Your solution is okay!")
    for k in ("Lean paranoid kernel", "lean4lean kernel", "nanoda kernel", "con-leche kernel", "con-ron kernel",
              "Lean default kernel"):
        assert f"{k} accepts the solution" in log, k

    # 4. records: witnesses, certificates, file comparison, inputs
    inputs = {(f["family"], f["name"]): f for f in load("inputs/kaplan-files.json")["files"]}
    assert len(inputs) == 41
    shapes = {}
    for p in sorted((ROOT / "witnesses").glob("*/*.jsonl")):
        f = inputs[(p.parent.name, p.stem + ".txt")]
        assert f["role"] == "selected"
        rows_w = jsonl(p.relative_to(ROOT))
        assert len(rows_w) <= f["shapes"]
        for r in rows_w:
            shapes[(r["family"], r["file"], r["index"])] = r
    assert len(shapes) == 3964 and sum(len(r["witnesses"]) for r in shapes.values()) == 6574
    assert sum(1 for r in shapes.values() if any(set(w["serves"]) == {"Hc", "Hh"} for w in r["witnesses"])) == 1354
    certs = [c for p in sorted((ROOT / "certificates").glob("*/*.jsonl")) for c in jsonl(p.relative_to(ROOT))]
    assert len(certs) == 5019 and len({c["name"] for c in certs}) == 5019
    per_shape = collections.defaultdict(list)
    for c in certs:
        s = shapes[(c["family"], c["file"], c["index"])]
        assert c["shape"] == s["shape"] and (c["Hc"], c["Hh"]) == (s["Hc"], s["Hh"])
        assert c["drat_trim"]["result"] == "s VERIFIED"
        per_shape[(c["family"], c["file"], c["index"])].append(c)
    for k, s in shapes.items():
        cs = per_shape[k]
        hh = [c for c in cs if c["mode"] == "Hh"]
        hc = [c for c in cs if c["mode"] == "Hc"]
        assert len(hh) == 1 and hh[0]["K"] == s["Hh"] + 1 and hh[0]["blocks"] == []
        assert s["Hh"] - 1 <= s["Hc"] <= s["Hh"]
        if s["Hc"] < s["Hh"]:
            assert len(hc) == 1 and hc[0]["K"] == s["Hc"] + 1
        else:
            assert not hc
    # Table 4 of the article
    t4 = {}
    for fam in GRID:
        cs = [c for c in certs if c["family"] == fam]
        t4[GRID[fam]] = (sum(1 for k in shapes if k[0] == fam), sum(len(r["witnesses"]) for k, r in shapes.items() if k[0] == fam),
                         sum(1 for c in cs if c["mode"] == "Hh"), sum(1 for c in cs if c["mode"] == "Hc"),
                         sum(len(c["blocks"]) for c in cs), max(c["cnf"]["clauses"] for c in cs))
    assert t4 == {"square": (1616, 2766, 1616, 460, 7267, 2926850), "hexagonal": (437, 808, 437, 100, 2126, 6588816),
                  "triangular": (1911, 3000, 1911, 495, 3894, 5869683)}, t4
    solvers = collections.Counter(c["solver"] for c in certs)
    assert solvers == {"cadical153": 4998, "glucose4": 16, "lingeling": 5}
    # Table 3 of the article: distribution of (Hc, Hh)
    dist = collections.Counter((r["Hc"], r["Hh"]) for r in shapes.values())
    assert dist == {(0, 0): 1084, (0, 1): 937, (1, 1): 1748, (1, 2): 99, (2, 2): 63, (2, 3): 8, (3, 3): 8,
                    (3, 4): 11, (4, 4): 6}, dist
    # Table 5: file comparison
    bridge = {r["name"]: r for r in jsonl("bridge/file-comparison.jsonl.gz")}
    assert set(bridge) == {c["name"] for c in certs}
    tot = collections.defaultdict(lambda: [0, 0, 0, collections.Counter()])
    for c in certs:
        b = bridge[c["name"]]
        assert b["status"] == "CNF_MULTISET_ISOMORPHIC" and b["K"] == c["K"] and b["mode"] == c["mode"]
        assert b["producer_sha256"] == c["cnf"]["sha256"] and b["producer_bytes"] == c["cnf"]["bytes"]
        assert (b["variables"], b["clauses"]) == (c["cnf"]["vars"], c["cnf"]["clauses"])
        t = tot[GRID[c["family"]]]
        t[0] += 1; t[1] += b["variables"]; t[2] += b["clauses"]; t[3][b["K"]] += 1
    t5 = {g: (v[0], v[1], v[2], [v[3][k] for k in range(1, 6)]) for g, v in tot.items()}
    assert t5 == {"square": (2076, 45711523, 178454670, [829, 1218, 24, 5, 0]),
                  "hexagonal": (537, 39687752, 168537425, [75, 326, 102, 19, 15]),
                  "triangular": (2406, 48014519, 191702313, [1117, 1240, 44, 3, 2])}, t5
    assert sum(c["cnf"]["bytes"] for c in certs) == by_id["upper-bounds"]["numbers"]["cnf_total_bytes"]
    assert sum(c["proof"]["bytes"] for c in certs) == by_id["upper-bounds"]["numbers"]["proof_total_bytes"]
    sample = load("ci/certificate-sample.json")["names"]
    assert set(sample) <= set(bridge) and len(sample) == len(set(sample))

    # 5. counts table against Table 6 of the article
    table = load("counts/table.json")["rows"]
    t6 = {r["case"]: (r["first"]["prefix_counts"], r["second"]["total"], r["first"]["total"]) for r in table}
    assert len(t6) == 30 and sum(1 for v in t6.values() if v[2] is not None) == 28
    assert t6["hex-15hex_3up-315-Hh"][1] == 13031023098920 and t6["hex-15hex_3up-315-Hc"][1] == 269859001
    assert t6["hex-11hex_3up-32-Hh"][1] == 7030233087 and t6["omino-17omino_2up-192-Hc"][1] == 2

    # 6. article: labels, references, citations, wording, PDF record
    tex = (ROOT / f"{PAPER}.tex").read_text()
    labels = re.findall(r"\\label\{([^}]+)\}", tex)
    assert len(labels) == len(set(labels)) and {c["paper_label"] for c in claims["claims"]} <= set(labels)
    assert set(re.findall(r"\\(?:ref|eqref)\{([^}]+)\}", tex)) <= set(labels)
    bib = set(re.findall(r"\\bibitem\{([^}]+)\}", tex))
    cited = {k.strip() for g in re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", tex) for k in g.split(",")}
    assert cited == bib, cited ^ bib
    assert tex.count("VERIFICATION-RECORD.md") == 1 and (ROOT / "VERIFICATION-RECORD.md").is_file()
    assert r"\author{Tatsuhiko Takimoto\\\small Independent researcher}" in tex and "Version 2.1, 23 October 2026" in tex
    assert "(draft)" not in tex
    assert not re.search(r"\b(?:R\d{3}|T\d{4}|Claude|Codex|mailbox|coordinator)\b", tex), "process label in article"
    assert not re.search(r"\b[0-9a-f]{40}\b", re.sub(r"\\nolinkurl\{[0-9a-f]{40}\}", "", tex)), "commit in article"
    for t in ("hh\\_sound\\_square", "hc\\_sound\\_tri", "6,574", "5,019", "3,964", "13,287"):
        assert t in tex, t
    pdf = load("pdf-validation.json")
    assert pdf["status"] == "PASS" and pdf["all_pages_viewed"] is True and pdf["pages"] == 15
    assert sha(ROOT / f"{PAPER}.pdf") == pdf["pdf_sha256"] and sha(ROOT / f"{PAPER}.tex") == pdf["source_sha256"]
    assert not pdf["overfull_boxes"] and not pdf["undefined_references"] and not pdf["unresolved_marks"]
    text = subprocess.run(["pdftotext", f"{PAPER}.pdf", "-"], cwd=ROOT, capture_output=True, text=True,
                          check=True).stdout
    assert "??" not in text and "Version 2.1" in text

    # 7. citation metadata
    cff = load("CITATION.cff")
    author = [{"family-names": "Takimoto", "given-names": "Tatsuhiko", "affiliation": "Independent researcher"}]
    assert cff["version"] == VERSION and cff["repository-code"] == REPOSITORY and cff["license"] == "Apache-2.0"
    assert cff["authors"] == author and cff["preferred-citation"]["authors"] == author
    assert cff["preferred-citation"]["license"] == "CC-BY-4.0" and cff["preferred-citation"]["version"] == "2.1"
    zen = load(".zenodo.json")
    assert zen["version"] == VERSION and zen["license"] == "cc-by-4.0"
    assert zen["creators"] == [{"name": "Tatsuhiko Takimoto", "affiliation": "Independent researcher"}]
    assert any(r["identifier"] == REPOSITORY for r in zen["related_identifiers"])
    assert REPOSITORY in (ROOT / "README.md").read_text()

    # 8. privacy
    from publication_privacy import scan_tree
    privacy = scan_tree(ROOT)
    assert not privacy["hits"], privacy["hits"]
    print(json.dumps(dict(status="PASS", version=VERSION, files=len(actual), claims=len(claims["claims"]),
                          shapes=len(shapes), witnesses=6574, certificates=len(certs), article_pages=pdf["pages"],
                          privacy_hits=0,
                          scope="Static closure, claims, record cross-checks (Tables 3-6), Lean file checks, article "
                                "consistency and privacy; ci_check.py and recheck_certificates.py re-run computations.")))


if __name__ == "__main__":
    main()
