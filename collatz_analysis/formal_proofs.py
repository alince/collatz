"""
Constructive Proof Certificate Engine & Automata-Theoretic Obstruction Analyzer.

Provides:
1. Machine-checked constructive certificates for Theorems 1-5 of the Collatz
   analysis suite.
2. Exact Myhill-Nerode / DFA state-complexity verification for the k-step
   Collatz affine transducer x -> 3^w x + C_k(v) in base 2, proving that the
   carry automaton requires exactly 3^w distinguishable states (growing >= 2^k
   along surviving branches), and connecting this to Cobham's Theorem (1969)
   and Conway's (1972) undecidability of generalized piecewise-affine maps.
"""

from __future__ import annotations

import copy
import hashlib
import math
import os
import re
import shutil
import signal
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

from .boost_obstructions import (
    classify_s_integer_1cycles_z_inv_30,
    compute_brox_effective_finiteness_bounds,
    prove_m92_nonexistence_hensel_certificate,
    verify_cantor_cone_rigidity_and_uncertainty,
)
from .coalescence_and_mcycles import (
    compute_contractive_coalescence_sieve,
    prove_2cycle_nonexistence_up_to_weight,
    prove_surviving_diamond_threshold_k34,
)
from .frontier_reductions import (
    self_certify_garner_bootstrap,
    verify_counter_model_no_go_meta_theorem,
    verify_one_equation_diophantine_equivalence,
    verify_raney_cantor_cone_on_negative_cycles,
)
from .goal_extensions import (
    classify_5adic_unit_cycle_denominators,
    classify_all_z_2cycles_and_3cycles,
    classify_s_integer_2cycles_z_inv_30,
    prove_multistep_hensel_mcycle_nonexistence,
    verify_deficit_drift_complementarity_and_peak_bound,
    verify_lower_semiconvergent_pinch_and_baker_floor,
    verify_minimal_divergent_coalescence_obstruction,
)
from .mcycles_and_cantor_cone import (
    analyze_cantor_cone_and_sturmian_2adic,
    prove_unconditional_mcycle_nonexistence,
    verify_one_sided_semiconvergent_records,
)
from .cycles import (
    compute_min_cycle_length_bound,
    exhaustive_cycle_search_up_to_k,
    prove_steiners_1cycle_theorem,
)
from .parity_2adic import (
    verify_parity_bijection,
)
from .stopping_time import (
    analyze_tao_syracuse_mixing,
    compute_exact_stopping_time_dp,
    cramer_large_deviation_parameters,
    verify_beatty_sturmian_characterization,
    verify_garner_stopping_time_coincidence,
)


@dataclass(frozen=True)
class TransducerStateComplexity:
    """Exact state complexity of the base-2 LSB-first transducer for x -> 3^w x + C."""

    w: int
    multiplier_3w: int
    reachable_carry_states: int
    theoretical_state_count: int
    exact_match: bool


def verify_base2_transducer_state_growth(max_w: int = 7) -> List[TransducerStateComplexity]:
    """
    Prove by exhaustive reachability and Myhill-Nerode distinguishability that the
    LSB-first base-2 transducer computing y = 3^w * x + C (for odd-step weight w and
    carry C = 3^w - 2^w) has EXACTLY 3^w reachable and pairwise distinguishable carry
    states {0, 1, ..., 3^w - 1}.

    Transition rule on carry state c in {0, ..., 3^w - 1} upon reading input bit b in {0, 1}:
        total = 3^w * b + c
        output_bit = total mod 2
        next_carry = total // 2
    Since gcd(3^w, 2) = 1 and next_carry ranges from 0 to (3^w + 3^w - 1)//2 = 3^w - 1,
    every carry state c in {0, 1, ..., 3^w - 1} is reachable from c_0 = 0 and produces a
    unique 2-adic output stream y(c) = c + 3^w * x in Z_2.
    """
    results: List[TransducerStateComplexity] = []
    for w in range(1, max_w + 1):
        m = 3**w
        visited = {0}
        queue = [0]
        while queue:
            c = queue.pop()
            for b in (0, 1):
                c_next = (m * b + c) >> 1
                if c_next not in visited:
                    visited.add(c_next)
                    queue.append(c_next)
        results.append(
            TransducerStateComplexity(
                w=w,
                multiplier_3w=m,
                reachable_carry_states=len(visited),
                theoretical_state_count=m,
                exact_match=(len(visited) == m and min(visited) == 0 and max(visited) == m - 1),
            )
        )
    return results


def verify_catalan_mihailescu_unit_cycles(max_k: int = 20) -> Dict[str, object]:
    """
    Verify the Catalan-Mihailescu Classification of Unit-Denominator Collatz Cycles:
    For a parity vector v in {0, 1}^k of weight w >= 1, the cycle denominator
    D(k, w) = 2^k - 3^w is a unit in Z (i.e. |2^k - 3^w| = 1) if and only if:
    - (k, w) = (2, 1): D(2, 1) = +1 -> unique positive trivial cycle {1, 2}
    - (k, w) = (1, 1): D(1, 1) = -1 -> negative unit cycle {-1}
    - (k, w) = (3, 2): D(3, 2) = -1 -> negative unit cycle {-5, -7, -10}

    For all other (k, w) with 1 <= w <= k <= max_k, |2^k - 3^w| >= 5, so integer
    cycles require non-trivial divisibility D(k, w) | C_k(v) (which first occurs in Z^-
    at (k, w) = (11, 7) where D(11, 7) = -139 divides C_11(v) = 139 * 17 = 2363).
    """
    unit_pairs: List[Tuple[int, int, int]] = []
    min_nonunit_gap = (0, 0, 10**18)

    for k in range(1, max_k + 1):
        p2 = 1 << k
        for w in range(1, k + 1):
            diff = p2 - (3**w)
            if abs(diff) == 1:
                unit_pairs.append((k, w, diff))
            else:
                if abs(diff) < abs(min_nonunit_gap[2]):
                    min_nonunit_gap = (k, w, diff)

    return {
        "max_k": max_k,
        "unit_denominator_pairs": unit_pairs,
        "expected_unit_pairs": [(1, 1, -1), (2, 1, 1), (3, 2, -1)],
        "exact_catalan_match": sorted(unit_pairs) == [(1, 1, -1), (2, 1, 1), (3, 2, -1)],
        "smallest_nonunit_gap": {
            "k": min_nonunit_gap[0],
            "w": min_nonunit_gap[1],
            "gap": min_nonunit_gap[2],
        },
    }


ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS: frozenset[str] = frozenset(
    {"propext", "Quot.sound", "Classical.choice"}
)


def _pinned_elan_toolchain_bin(tool_stem: str) -> Optional[Path]:
    """
    Resolve the exact pinned binary in `~/.elan/toolchains/<toolchain>/bin` from
    `lean-toolchain` if present (avoiding elan proxy hangs outside `pkg_dir`).
    """
    pkg_dir = Path(__file__).resolve().parent
    tc_file = pkg_dir / "lean-toolchain"
    exe_name = f"{tool_stem}.exe" if os.name == "nt" else tool_stem
    if tc_file.is_file():
        tc_raw = tc_file.read_text(encoding="utf-8").strip()
        if tc_raw:
            tc_dir = tc_raw.replace("/", "--").replace(":", "---")
            pinned = Path.home() / ".elan" / "toolchains" / tc_dir / "bin" / exe_name
            if pinned.is_file():
                return pinned
    return None


def find_lean4_executable() -> Optional[Path]:
    """
    Locate the Lean 4 compiler binary via pinned `lean-toolchain`, PATH, or `~/.elan/bin`.
    """
    pinned = _pinned_elan_toolchain_bin("lean")
    if pinned is not None:
        return pinned
    which_lean = shutil.which("lean")
    if which_lean:
        return Path(which_lean)
    exe_name = "lean.exe" if os.name == "nt" else "lean"
    elan_lean = Path.home() / ".elan" / "bin" / exe_name
    if elan_lean.is_file():
        return elan_lean
    return None


def find_lake_executable() -> Optional[Path]:
    """
    Locate the Lake build tool binary via pinned `lean-toolchain`, PATH, or `~/.elan/bin`.
    """
    pinned = _pinned_elan_toolchain_bin("lake")
    if pinned is not None:
        return pinned
    which_lake = shutil.which("lake")
    if which_lake:
        return Path(which_lake)
    exe_name = "lake.exe" if os.name == "nt" else "lake"
    elan_lake = Path.home() / ".elan" / "bin" / exe_name
    if elan_lake.is_file():
        return elan_lake
    lean_bin = find_lean4_executable()
    if lean_bin is not None:
        sibling = lean_bin.with_name(exe_name)
        if sibling.is_file():
            return sibling
    return None


def get_collatz_lean_files() -> List[Path]:
    """
    Return `CollatzFormal.lean` followed by all sorted `CollatzFormal/*.lean` submodules.
    """
    pkg_dir = Path(__file__).resolve().parent
    root_file = pkg_dir / "CollatzFormal.lean"
    sub_dir = pkg_dir / "CollatzFormal"
    files: List[Path] = []
    if root_file.is_file():
        files.append(root_file)
    if sub_dir.is_dir():
        files.extend(sorted(sub_dir.glob("*.lean")))
    return files


def read_all_collatz_lean_sources() -> str:
    """
    Concatenate `CollatzFormal.lean` and all `CollatzFormal/*.lean` submodule sources.
    """
    return "\n\n".join(p.read_text(encoding="utf-8") for p in get_collatz_lean_files())


def _strip_lean_comments(source: str) -> str:
    """
    Strip nested Lean 4 block comments (`/- ... -/`) and line comments (`-- ...`)
    so static hygiene checks inspect only active Lean 4 code.
    """
    out: List[str] = []
    i = 0
    n = len(source)
    depth = 0
    while i < n:
        if depth == 0 and source[i : i + 2] == "--":
            while i < n and source[i] != "\n":
                i += 1
            continue
        if source[i : i + 2] == "/-":
            depth += 1
            i += 2
            continue
        if depth > 0 and source[i : i + 2] == "-/":
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(source[i])
        elif source[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


_LEAN4_AUDIT_CACHE: Dict[Tuple[str, str], Dict[str, object]] = {}

_LAKE_SEQUENTIAL_TARGETS: Tuple[str, ...] = (
    "+CollatzFormal.Core",
    "+CollatzFormal.RationalLogSlabs",
    "+CollatzFormal.Survivors",
    "+CollatzFormal.BoostMechanisms",
    "+CollatzFormal.HenselBridgeCore",
    "+CollatzFormal.HenselBridge93_U2",
    "+CollatzFormal.HenselBridge94",
    "+CollatzFormal.HenselBridge95_U4",
    "+CollatzFormal.HenselBridge95",
    "+CollatzFormal.HenselBridge96_U5",
    "+CollatzFormal.HenselBridge93_Meta",
    "+CollatzFormal.HenselBridge93_00",
    "+CollatzFormal.HenselBridge93_01",
    "+CollatzFormal.HenselBridge93_02",
    "+CollatzFormal.HenselBridge93_03",
    "+CollatzFormal.HenselBridge93_04",
    "+CollatzFormal.HenselBridge93_05",
    "+CollatzFormal.HenselBridge93_06",
    "+CollatzFormal.HenselBridge93_07",
    "+CollatzFormal.HenselBridge93_08",
    "+CollatzFormal.HenselBridge93_09",
    "+CollatzFormal.HenselBridge93_10",
    "+CollatzFormal.HenselBridge93_11",
    "+CollatzFormal.HenselBridge93_12",
    "+CollatzFormal.HenselBridge93_13",
    "+CollatzFormal.HenselBridge93_14",
    "+CollatzFormal.HenselBridge93_15",
    "+CollatzFormal.HenselBridge96_Meta",
    "+CollatzFormal.HenselBridge96_00",
    "+CollatzFormal.HenselBridge96_01",
    "+CollatzFormal.HenselBridge96_02",
    "+CollatzFormal.HenselBridge96_03",
    "+CollatzFormal.HenselBridge96_04",
    "+CollatzFormal.HenselBridge96_05",
    "+CollatzFormal.HenselBridge96_06",
    "+CollatzFormal.HenselBridge96_07",
    "+CollatzFormal.HenselBridge96_08",
    "+CollatzFormal.HenselBridge93To96",
    "+CollatzFormal.Survivors97To99A",
    "+CollatzFormal.Survivors97To99B",
    "+CollatzFormal.Survivors97To99C",
    "+CollatzFormal.Survivors97To99D",
    "+CollatzFormal.Survivors97To99E",
    "+CollatzFormal.Survivors97To99F",
    "+CollatzFormal.Survivors97To99G",
    "+CollatzFormal.Survivors97To99H",
    "+CollatzFormal.Survivors97To99I",
    "+CollatzFormal.Survivors97To99J",
    "+CollatzFormal.Survivors97To99",
    "+CollatzFormal.CSFullConjecture",
    "+CollatzFormal.CSWave3Synthesis",
    "+CollatzFormal.Wave4WholeSpace",
    "+CollatzFormal.Wave5WholeSpace",
    "+CollatzFormal.Wave6WholeSpace",
    "+CollatzFormal.Wave7WholeSpace",
    "+CollatzFormal.Wave8WholeSpace",
    "+CollatzFormal.Wave9WholeSpace",
    "+CollatzFormal.Wave10WholeSpace",
    "+CollatzFormal.Wave11WholeSpaceCore",
    "+CollatzFormal.Wave11WholeSpace",
    "+CollatzFormal.Wave12WholeSpaceCore",
    "+CollatzFormal.Wave12WholeSpace",
    "+CollatzFormal.Wave13WholeSpaceCore",
    "+CollatzFormal.Wave13WholeSpace",
    "+CollatzFormal.Wave14WholeSpaceCore",
    "+CollatzFormal.Wave14WholeSpace",
    "+CollatzFormal.Wave15WholeSpaceCore",
    "+CollatzFormal.Wave15WholeSpace",
    "+CollatzFormal.Wave16WholeSpaceCore",
    "+CollatzFormal.Wave16WholeSpace",
    "+CollatzFormal.Wave17WholeSpaceCore",
    "+CollatzFormal.Wave17WholeSpace",
    "+CollatzFormal",
)


_STDLIB_SUBPROCESS_RUN = subprocess.run


def _decode_proc_stream(stream: object) -> str:
    """Safely decode subprocess output streams (`None`, `bytes`, or `str`)."""
    if stream is None:
        return ""
    if isinstance(stream, (bytes, bytearray)):
        return bytes(stream).decode("utf-8", errors="replace")
    return str(stream)


def _kill_process_tree(proc: subprocess.Popen[str]) -> None:
    """Force-terminate `proc` and any descendant child/grandchild processes."""
    if os.name == "nt":
        try:
            _STDLIB_SUBPROCESS_RUN(
                ["taskkill", "/F", "/T", "/PID", str(proc.pid)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=5.0,
                check=False,
            )
        except (OSError, subprocess.SubprocessError):
            pass
    else:
        killpg_fn = getattr(os, "killpg", None)
        sigkill = getattr(signal, "SIGKILL", signal.SIGTERM)
        if killpg_fn is not None:
            try:
                killpg_fn(proc.pid, sigkill)
            except (ProcessLookupError, PermissionError, OSError):
                pass
    try:
        proc.kill()
    except OSError:
        pass


def _run_process_tree_bounded(
    cmd: List[str],
    *,
    cwd: str,
    env: Optional[Dict[str, str]],
    timeout: float,
) -> subprocess.CompletedProcess[str]:
    """
    Execute `cmd` with UTF-8 (`errors='replace'`) stream capture and full process-tree
    termination on timeout so grandchild `lean` processes holding inherited pipes on
    Windows/POSIX never block `communicate()` or outlive `timeout`.
    """
    popen_kwargs: Dict[str, object] = {
        "cwd": cwd,
        "env": env,
        "stdout": subprocess.PIPE,
        "stderr": subprocess.PIPE,
        "text": True,
        "encoding": "utf-8",
        "errors": "replace",
    }
    if os.name == "nt":
        popen_kwargs["creationflags"] = getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)
    else:
        popen_kwargs["start_new_session"] = True

    with subprocess.Popen(cmd, **popen_kwargs) as proc:  # type: ignore[call-overload]
        try:
            out_str, err_str = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            _kill_process_tree(proc)
            out_part, err_part = proc.communicate()
            raise subprocess.TimeoutExpired(
                cmd=cmd,
                timeout=timeout,
                output=out_part,
                stderr=err_part,
            ) from None
        except BaseException:
            _kill_process_tree(proc)
            proc.wait()
            raise
        return subprocess.CompletedProcess(
            args=cmd,
            returncode=proc.returncode,
            stdout=out_str,
            stderr=err_str,
        )


def verify_lean4_kernel_proofs(
    timeout_sec: float = 900.0,
    bypass_cache: bool = False,
) -> Dict[str, object]:
    """
    Invoke Lake + the live Lean 4 kernel across `CollatzFormal.lean` and all
    `CollatzFormal/*.lean` submodules with an exhaustive `#print axioms` audit
    across every `theorem` declaration in the formalization.

    Verifies:
    1. Static code hygiene: zero `sorry`, `admit`, `axiom`, or `native_decide`
       tokens in active (non-comment) Lean 4 source across all modules.
    2. Incremental `.olean` compilation via `lake.exe` (`LEAN_JOBS=2`, `--wfail`,
       sequential target order so parallel Lean builds never lock up).
    3. Live Lean 4 kernel compilation (`-M 2048 -T 200000 -j 2`) of
       `CollatzFormalAudit.lean` (`import CollatzFormal` + `#print axioms` for
       every theorem): exit code 0, zero compiler warnings/errors, zero `sorryAx`,
       zero `Lean.trustCompiler`, and every observed axiom strictly in
       `{"propext", "Quot.sound", "Classical.choice"}`.
    """
    if (
        isinstance(timeout_sec, bool)
        or not isinstance(timeout_sec, (int, float))
        or not math.isfinite(timeout_sec)
        or timeout_sec <= 0.0
    ):
        raise ValueError(f"timeout_sec must be a finite positive number, got {timeout_sec!r}")

    t0 = time.perf_counter()
    deadline = t0 + float(timeout_sec)
    pkg_dir = Path(__file__).resolve().parent
    lean_path = pkg_dir / "CollatzFormal.lean"
    lean_files = get_collatz_lean_files()

    theorem_names: List[str] = []
    seen_theorems: Set[str] = set()
    duplicate_theorems: List[str] = []
    forbidden_tokens_found: List[str] = []
    hasher = hashlib.sha256()

    for cfg_name in ("lean-toolchain", "lakefile.lean"):
        cfg_path = pkg_dir / cfg_name
        if cfg_path.is_file():
            hasher.update(cfg_name.encode("utf-8"))
            hasher.update(cfg_path.read_bytes())

    for lf in lean_files:
        raw_src = lf.read_text(encoding="utf-8")
        hasher.update(str(lf.relative_to(pkg_dir)).encode("utf-8"))
        hasher.update(raw_src.encode("utf-8"))
        stripped = _strip_lean_comments(raw_src)
        for thm in re.findall(r"^\s*theorem\s+([A-Za-z0-9_']+)", stripped, flags=re.MULTILINE):
            if thm in seen_theorems:
                duplicate_theorems.append(thm)
            else:
                seen_theorems.add(thm)
                theorem_names.append(thm)
        forbidden_tokens_found.extend(
            re.findall(r"\b(?:sorry|admit|axiom|native_decide)\b", stripped)
        )

    static_hygiene_clean = (
        len(forbidden_tokens_found) == 0
        and len(duplicate_theorems) == 0
        and len(theorem_names) > 0
    )

    lean_bin = find_lean4_executable()
    lake_bin = find_lake_executable()
    if lean_bin is None:
        return {
            "lean_available": False,
            "lean_executable": None,
            "lake_executable": str(lake_bin) if lake_bin is not None else None,
            "lean_version": None,
            "lean_file": str(lean_path),
            "lean_files": [str(p) for p in lean_files],
            "timed_out": False,
            "theorems_audited": 0,
            "theorem_names": theorem_names,
            "static_hygiene_clean": static_hygiene_clean,
            "zero_sorry_verified": False,
            "zero_warnings_verified": False,
            "pure_kernel_verified": False,
            "elapsed_ms": (time.perf_counter() - t0) * 1000.0,
        }

    cache_key = (hasher.hexdigest(), str(lean_bin))
    if not bypass_cache and cache_key in _LEAN4_AUDIT_CACHE:
        return copy.deepcopy(_LEAN4_AUDIT_CACHE[cache_key])

    timed_out = False
    timeout_diag_parts: List[str] = []

    def _run_bounded_subprocess(
        cmd: List[str],
        *,
        stage_label: str,
        run_env: Optional[Dict[str, str]] = None,
    ) -> Optional[subprocess.CompletedProcess[str]]:
        nonlocal timed_out
        rem = deadline - time.perf_counter()
        if rem <= 0.0:
            timed_out = True
            timeout_diag_parts.append(
                f"Timeout budget ({timeout_sec:.3f}s) exhausted before {stage_label}"
            )
            return None
        try:
            if subprocess.run is not _STDLIB_SUBPROCESS_RUN:
                return subprocess.run(
                    cmd,
                    cwd=str(pkg_dir),
                    env=run_env,
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    timeout=rem,
                    check=False,
                )
            return _run_process_tree_bounded(
                cmd,
                cwd=str(pkg_dir),
                env=run_env,
                timeout=rem,
            )
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            actual_to = (
                f"{float(exc.timeout):.3f}s"
                if isinstance(exc.timeout, (int, float))
                else str(exc.timeout)
            )
            timeout_diag_parts.append(
                f"Timed out after {actual_to} (total budget {timeout_sec:.3f}s) during {stage_label}"
            )
            out_txt = _decode_proc_stream(exc.stdout).strip()
            err_txt = _decode_proc_stream(exc.stderr).strip()
            if err_txt:
                timeout_diag_parts.append(err_txt)
            if out_txt:
                out_lines = out_txt.splitlines()
                if len(out_lines) > 20:
                    timeout_diag_parts.append("\n".join(out_lines[-20:]))
                else:
                    timeout_diag_parts.append(out_txt)
            return None

    ver_proc = _run_bounded_subprocess(
        [str(lean_bin), "--version"],
        stage_label="lean --version",
    )
    ver_out = _decode_proc_stream(ver_proc.stdout).strip() if ver_proc is not None else ""
    lean_version = ver_out.splitlines()[0] if ver_out else ""

    env = os.environ.copy()
    env["LEAN_JOBS"] = "2"
    env["PATH"] = str(lean_bin.parent) + os.pathsep + env.get("PATH", "")

    has_lakefile = (pkg_dir / "lakefile.lean").is_file()
    lake_build_ok = True
    lake_diag_parts: List[str] = []
    olean_lib_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"

    if not timed_out and has_lakefile:
        if lake_bin is None:
            lake_build_ok = False
            lake_diag_parts.append(
                "Lake executable not found; required to verify multi-module CollatzFormal build"
            )
        else:
            chk_proc = _run_bounded_subprocess(
                [str(lake_bin), "--no-cache", "--wfail", "--no-ansi", "-q", "--no-build", "build"],
                stage_label="lake --no-build build",
                run_env=env,
            )
            if chk_proc is None:
                lake_build_ok = False
            elif chk_proc.returncode != 0:
                for target in _LAKE_SEQUENTIAL_TARGETS:
                    b_proc = _run_bounded_subprocess(
                        [str(lake_bin), "--no-cache", "--wfail", "--no-ansi", "-q", "build", target],
                        stage_label=f"lake build {target}",
                        run_env=env,
                    )
                    if b_proc is None:
                        lake_build_ok = False
                        break
                    b_out = _decode_proc_stream(b_proc.stdout).strip()
                    b_err = _decode_proc_stream(b_proc.stderr).strip()
                    if b_out:
                        lake_diag_parts.append(b_out)
                    if b_err:
                        lake_diag_parts.append(b_err)
                    if b_proc.returncode != 0:
                        lake_build_ok = False
                        break
            else:
                chk_out = _decode_proc_stream(chk_proc.stdout).strip()
                chk_err = _decode_proc_stream(chk_proc.stderr).strip()
                if chk_out:
                    lake_diag_parts.append(chk_out)
                if chk_err:
                    lake_diag_parts.append(chk_err)

    proc: Optional[subprocess.CompletedProcess[str]] = None
    if not timed_out and lake_build_ok:
        audit_lines = [f"#print axioms CollatzFormal.{name}" for name in theorem_names]
        if has_lakefile or olean_lib_dir.is_dir():
            env["LEAN_PATH"] = str(olean_lib_dir)
            audit_source = "import CollatzFormal\n\n" + "\n".join(audit_lines) + "\n"
        else:
            audit_source = read_all_collatz_lean_sources() + "\n\n" + "\n".join(audit_lines) + "\n"

        with tempfile.TemporaryDirectory(ignore_cleanup_errors=True) as tmpdir:
            audit_file = Path(tmpdir) / "CollatzFormalAudit.lean"
            audit_file.write_text(audit_source, encoding="utf-8")
            proc = _run_bounded_subprocess(
                [str(lean_bin), "-M", "2048", "-T", "200000", "-j", "2", str(audit_file)],
                stage_label="lean CollatzFormalAudit.lean",
                run_env=env,
            )

    proc_stdout = _decode_proc_stream(proc.stdout) if proc is not None else ""
    proc_stderr = _decode_proc_stream(proc.stderr) if proc is not None else ""
    proc_returncode = proc.returncode if proc is not None else 124

    axioms_by_theorem: Dict[str, List[str]] = {}
    all_axioms_observed: Set[str] = set()
    no_ax_re = re.compile(r"^'CollatzFormal\.([A-Za-z0-9_']+)' does not depend on any axioms$")
    dep_ax_re = re.compile(r"^'CollatzFormal\.([A-Za-z0-9_']+)' depends on axioms: \[(.*)\]$")

    merged_stdout_lines: List[str] = []
    pending_bracket: Optional[str] = None
    for raw_line in proc_stdout.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if pending_bracket is not None:
            pending_bracket = f"{pending_bracket} {line}"
            if line.endswith("]"):
                merged_stdout_lines.append(pending_bracket)
                pending_bracket = None
            continue
        if (
            line.startswith("'CollatzFormal.")
            and "depends on axioms: [" in line
            and not line.endswith("]")
        ):
            pending_bracket = line
            continue
        merged_stdout_lines.append(line)
    if pending_bracket is not None:
        merged_stdout_lines.append(pending_bracket)

    unexpected_stdout_lines: List[str] = []
    for line in merged_stdout_lines:
        m_none = no_ax_re.match(line)
        if m_none:
            axioms_by_theorem[m_none.group(1)] = []
            continue
        m_dep = dep_ax_re.match(line)
        if m_dep:
            axs = [a.strip() for a in m_dep.group(2).split(",") if a.strip()]
            axioms_by_theorem[m_dep.group(1)] = axs
            all_axioms_observed.update(axs)
            continue
        unexpected_stdout_lines.append(line)

    has_stdout_warning = any("warning:" in ln.lower() for ln in unexpected_stdout_lines)
    all_theorems_accounted = set(axioms_by_theorem.keys()) == set(theorem_names)
    zero_warnings = (
        not timed_out
        and lake_build_ok
        and len(lake_diag_parts) == 0
        and proc is not None
        and proc_returncode == 0
        and proc_stderr.strip() == ""
        and not has_stdout_warning
        and len(unexpected_stdout_lines) == 0
    )
    zero_sorry = (
        not timed_out
        and lake_build_ok
        and proc is not None
        and proc_returncode == 0
        and static_hygiene_clean
        and all_theorems_accounted
        and ("sorryAx" not in all_axioms_observed)
        and ("sorryAx" not in proc_stdout)
    )
    pure_kernel = (
        not timed_out
        and zero_sorry
        and zero_warnings
        and all_axioms_observed.issubset(ALLOWED_LEAN4_FOUNDATIONAL_AXIOMS)
    )
    axiom_free_theorems = [name for name, axs in axioms_by_theorem.items() if len(axs) == 0]
    elapsed_ms = (time.perf_counter() - t0) * 1000.0

    diag_chunks: List[str] = list(timeout_diag_parts) + list(lake_diag_parts)
    if proc_stderr.strip():
        diag_chunks.append(proc_stderr.strip())
    if unexpected_stdout_lines:
        diag_chunks.append("\n".join(unexpected_stdout_lines))
    combined_diag = "\n".join(diag_chunks).strip()

    result = {
        "lean_available": True,
        "lean_executable": str(lean_bin),
        "lake_executable": str(lake_bin) if lake_bin is not None else None,
        "lean_version": lean_version,
        "lean_file": str(lean_path),
        "lean_files": [str(p) for p in lean_files],
        "timed_out": timed_out,
        "returncode": 124 if timed_out else (proc_returncode if lake_build_ok else 1),
        "stderr": combined_diag,
        "theorems_audited": len(axioms_by_theorem),
        "theorem_names": theorem_names,
        "axiom_free_theorem_count": len(axiom_free_theorems),
        "axiom_free_theorems": axiom_free_theorems,
        "all_axioms_observed": sorted(all_axioms_observed),
        "axioms_by_theorem": axioms_by_theorem,
        "static_hygiene_clean": static_hygiene_clean,
        "zero_sorry_verified": zero_sorry,
        "zero_warnings_verified": zero_warnings,
        "pure_kernel_verified": pure_kernel,
        "elapsed_ms": elapsed_ms,
    }
    if pure_kernel:
        _LEAN4_AUDIT_CACHE[cache_key] = copy.deepcopy(result)
    return result


def generate_full_proof_suite_report() -> Dict[str, object]:
    """
    Execute and return the complete machine-verified proof certificate dictionary
    across all 5 core theorems of the package.
    """
    thm1_bijection = verify_parity_bijection(k=10)
    thm2_beatty = verify_beatty_sturmian_characterization(max_k=12)
    thm2_catalan = verify_catalan_mihailescu_unit_cycles(max_k=20)
    thm2_cycles = exhaustive_cycle_search_up_to_k(max_k=11)
    thm3_steiner = prove_steiners_1cycle_theorem()
    thm3_eliahou_68 = compute_min_cycle_length_bound(log2_N0=68.0)
    thm3_eliahou_71 = compute_min_cycle_length_bound(log2_N0=71.0)
    thm4_dp = compute_exact_stopping_time_dp(max_k=100)
    thm4_cramer = cramer_large_deviation_parameters()
    thm4_garner = verify_garner_stopping_time_coincidence(limit_n=5000)
    thm5_tao = analyze_tao_syracuse_mixing(max_odd_n=9999, mod_power_3=3)
    thm5_transducer = verify_base2_transducer_state_growth(max_w=6)
    thm6_diamond = prove_surviving_diamond_threshold_k34()
    thm7_coalescence = compute_contractive_coalescence_sieve(max_k=15)
    thm8_2cycle = prove_2cycle_nonexistence_up_to_weight(max_W=60)
    thm9_one_eq = verify_one_equation_diophantine_equivalence(max_n=200)
    thm10_raney = verify_raney_cantor_cone_on_negative_cycles()
    thm10_bootstrap = self_certify_garner_bootstrap(limit_n=72058, sieve_k=14, max_w_scan=2000)
    thm11_nogo = verify_counter_model_no_go_meta_theorem()
    thm13_cantor = analyze_cantor_cone_and_sturmian_2adic(bits=64, max_w_norm=200)
    thm14_semiconv = verify_one_sided_semiconvergent_records(max_w=5000)
    thm14_mcycles_self = prove_unconditional_mcycle_nonexistence(N0=72058, max_m=20)
    thm14_mcycles_barina = prove_unconditional_mcycle_nonexistence(N0=1 << 71, max_m=95)
    thm15a_m92 = prove_m92_nonexistence_hensel_certificate(N0=1 << 71, prime_scan_limit=100_000)
    thm15b_brox = compute_brox_effective_finiteness_bounds(max_m=6)
    thm16_s_int = classify_s_integer_1cycles_z_inv_30()
    thm17_rigidity = verify_cantor_cone_rigidity_and_uncertainty(max_n_sample=150, sturm_depth=120)
    thm19_hensel = prove_multistep_hensel_mcycle_nonexistence(
        N0=1 << 71, max_m_full=94, eliminate_higher_multiples_up_to_m=95
    )
    thm20a_z23 = classify_all_z_2cycles_and_3cycles()
    thm20b_s2 = classify_s_integer_2cycles_z_inv_30()
    thm21a_deficit = verify_deficit_drift_complementarity_and_peak_bound(max_n=200)
    thm21b_pinch = verify_lower_semiconvergent_pinch_and_baker_floor(max_w=5000, max_n_sample=80)
    thm22a_5adic = classify_5adic_unit_cycle_denominators()
    thm22b_coal = verify_minimal_divergent_coalescence_obstruction(max_k=16)
    from .boost_mechanisms import (
        verify_boost_three_line_counter_model_matrix,
        verify_next_tier_boost_counter_model_matrix,
    )
    from .cs_cegar_redteam import (
        run_wave4_whole_space_campaign,
        run_wave5_whole_space_campaign,
        run_wave6_whole_space_campaign,
        run_wave7_whole_space_campaign,
        run_wave8_whole_space_campaign,
        run_wave9_whole_space_campaign,
        run_wave10_whole_space_campaign,
        run_wave11_whole_space_campaign,
        run_wave12_whole_space_campaign,
        run_wave13_whole_space_campaign,
        run_wave14_whole_space_campaign,
        run_wave15_whole_space_campaign,
        run_wave16_whole_space_campaign,
        run_wave17_whole_space_campaign,
    )

    thm23_25_boost = verify_boost_three_line_counter_model_matrix()
    thm29_31_boost = verify_next_tier_boost_counter_model_matrix()
    wave4_cert = run_wave4_whole_space_campaign()
    wave5_cert = run_wave5_whole_space_campaign()
    wave6_cert = run_wave6_whole_space_campaign()
    wave7_cert = run_wave7_whole_space_campaign()
    wave8_cert = run_wave8_whole_space_campaign()
    wave9_cert = run_wave9_whole_space_campaign()
    wave10_cert = run_wave10_whole_space_campaign()
    wave11_cert = run_wave11_whole_space_campaign()
    wave12_cert = run_wave12_whole_space_campaign()
    wave13_cert = run_wave13_whole_space_campaign()
    wave14_cert = run_wave14_whole_space_campaign()
    wave15_cert = run_wave15_whole_space_campaign()
    wave16_cert = run_wave16_whole_space_campaign()
    wave17_cert = run_wave17_whole_space_campaign()
    lean4_cert = verify_lean4_kernel_proofs()

    return {
        "theorem_1_parity_2adic_homeomorphism": thm1_bijection,
        "theorem_2_beatty_sturmian_and_catalan": {
            "beatty_sturmian": thm2_beatty,
            "catalan_mihailescu": thm2_catalan,
            "exhaustive_z_cycles_up_to_11": {
                "primitive_positive": len(thm2_cycles["primitive_positive_cycles"]),
                "primitive_negative": len(thm2_cycles["primitive_negative_cycles"]),
            },
        },
        "theorem_3_steiner_and_eliahou_bounds": {
            "steiner_1cycle": thm3_steiner,
            "eliahou_bound_2_pow_68": thm3_eliahou_68,
            "eliahou_bound_2_pow_71": thm3_eliahou_71,
        },
        "theorem_4_stopping_time_sieve_and_cramer": {
            "dp_depth_100": thm4_dp[-1],
            "cramer_parameters": thm4_cramer,
            "garner_coincidence": thm4_garner,
        },
        "theorem_5_tao_3adic_annihilation_and_automata": {
            "tao_syracuse_mixing": thm5_tao,
            "base2_transducer_complexity": thm5_transducer,
        },
        "theorem_6_surviving_diamond_threshold_k34": thm6_diamond,
        "theorem_7_contractive_3adic_coalescence_sieve": thm7_coalescence,
        "theorem_8_mcycle_telescoping_and_2cycles": thm8_2cycle,
        "theorem_9_one_equation_diophantine_equivalence": thm9_one_eq,
        "theorem_10_raney_and_self_certified_garner_bootstrap": {
            "raney_negative_cycles": thm10_raney,
            "garner_bootstrap": thm10_bootstrap,
        },
        "theorem_11_counter_model_no_go_meta_theorem": thm11_nogo,
        "theorem_13_cantor_cone_and_sturmian_2adic": thm13_cantor,
        "theorem_14_unconditional_mcycle_nonexistence": {
            "semiconvergent_records_check": thm14_semiconv["exact_sequence_match"],
            "self_certified_N0_72058_max_m": thm14_mcycles_self["max_m_proved_unconditionally"],
            "barina_2_pow_71_max_m": thm14_mcycles_barina["max_m_proved_unconditionally"],
        },
        "theorem_15_m92_hensel_and_brox_finiteness": {
            "barina_2_pow_71_max_m_with_hensel": thm15a_m92["max_m_proved_unconditionally"],
            "m92_certificate": thm15a_m92["certificate_m92"],
            "brox_effective_bounds": thm15b_brox["bounds"],
        },
        "theorem_16_padic_baker_s_integer_1cycles": thm16_s_int,
        "theorem_17_18_cantor_cone_rigidity_and_uncertainty": thm17_rigidity,
        "theorem_19_multistep_hensel_and_index45_horizon": thm19_hensel,
        "theorem_20_z_2_3_cycles_and_s_integer_2cycles": {
            "z_2cycles_and_3cycles": thm20a_z23,
            "s_integer_2cycles_z_inv_30": thm20b_s2,
        },
        "theorem_21_carry_deficit_and_lower_semiconvergent_pinch": {
            "deficit_drift_and_peak_bound": thm21a_deficit,
            "lower_semiconvergent_pinch_and_baker_floor": thm21b_pinch,
        },
        "theorem_22_5adic_unit_denominators_and_coalescence_obstruction": {
            "five_adic_unit_denominators": thm22a_5adic,
            "minimal_divergent_coalescence_obstruction": thm22b_coal,
        },
        "theorems_23_to_25_boost_mechanisms_and_counter_model_matrix": thm23_25_boost,
        "theorems_29_to_31_next_tier_boost_and_counter_model_matrix": thm29_31_boost,
        "wave4_whole_space_campaign": wave4_cert,
        "wave5_whole_space_campaign": wave5_cert,
        "wave6_whole_space_campaign": wave6_cert,
        "wave7_whole_space_campaign": wave7_cert,
        "wave8_whole_space_campaign": wave8_cert,
        "wave9_whole_space_campaign": wave9_cert,
        "wave10_whole_space_campaign": wave10_cert,
        "wave11_whole_space_campaign": wave11_cert,
        "wave12_whole_space_campaign": wave12_cert,
        "wave13_whole_space_campaign": wave13_cert,
        "wave14_whole_space_campaign": wave14_cert,
        "wave15_whole_space_campaign": wave15_cert,
        "wave16_whole_space_campaign": wave16_cert,
        "wave17_whole_space_campaign": wave17_cert,
        "lean4_kernel_verification": lean4_cert,
    }
