#!/usr/bin/env python3
"""Named pattern profiles for the V3 and V5 source scanners."""

from __future__ import annotations

import re

from lean_source_scanner import ScanPattern


V3_PATTERNS: tuple[ScanPattern, ...] = (
    ScanPattern(
        "v3.sorry",
        "placeholder",
        r"\bsorry\b",
        "Lean sorry placeholder token",
    ),
    ScanPattern(
        "v3.admit",
        "placeholder",
        r"\badmit\b",
        "Lean admit placeholder token",
    ),
    ScanPattern(
        "v3.sorryAx",
        "placeholder",
        r"\bsorryAx\b",
        "direct reference to Lean's sorry axiom",
    ),
    ScanPattern(
        "v3.proof_wanted",
        "placeholder",
        r"\bproof_wanted\b",
        "proof_wanted placeholder convention",
    ),
    ScanPattern(
        "v3.exit",
        "source_truncation",
        r"(?<![A-Za-z0-9_'])#exit\b",
        "mid-file #exit source truncation",
    ),
    ScanPattern(
        "v3.stop",
        "placeholder_marker",
        r"\bstop\b",
        "stop marker requiring contextual review",
        flags=re.MULTILINE | re.IGNORECASE,
    ),
    ScanPattern(
        "v3.todo",
        "work_marker",
        r"\bTODO\b",
        "TODO marker",
        flags=re.MULTILINE | re.IGNORECASE,
    ),
    ScanPattern(
        "v3.wip",
        "work_marker",
        r"\bWIP\b",
        "work-in-progress marker",
        flags=re.MULTILINE | re.IGNORECASE,
    ),
    ScanPattern(
        "v3.exercise_sorry_marker",
        "ledger_marker",
        r"\bEXERCISE-SORRY\b",
        "in-source exercise placeholder ledger marker",
    ),
    ScanPattern(
        "v3.appendix_unresolved_marker",
        "ledger_marker",
        r"\bAPPENDIX-UNRESOLVED-\d+\b",
        "appendix unresolved ledger marker",
    ),
    ScanPattern(
        "v3.external_sorry_marker",
        "legacy_marker",
        r"\bEXTERNAL-SORRY\b",
        "legacy marker expected to be extinct",
    ),
    ScanPattern(
        "v3.forward_sorry_marker",
        "legacy_marker",
        r"\bFORWARD-SORRY-\d+\b",
        "legacy forward-sorry marker expected to be extinct",
    ),
    ScanPattern(
        "v3.unresolved_proof_marker",
        "legacy_marker",
        r"\bUNRESOLVED-PROOF-\d+\b",
        "legacy unresolved-proof marker expected to be extinct",
    ),
)


V5_PATTERNS: tuple[ScanPattern, ...] = (
    ScanPattern(
        "v5.axiom",
        "declaration_escape",
        r"\baxiom\b",
        "custom axiom declaration or textual mention",
    ),
    ScanPattern(
        "v5.opaque",
        "declaration_surface",
        r"\bopaque\b",
        "opaque declaration or textual mention",
    ),
    ScanPattern(
        "v5.irreducible_def",
        "declaration_surface",
        r"\birreducible_def\b",
        "irreducible definition (elaborates an internal opaque wrapper)",
    ),
    ScanPattern(
        "v5.native_decide",
        "kernel_bypass",
        r"\bnative_decide\b",
        "native_decide proof path",
    ),
    ScanPattern(
        "v5.unsafe",
        "unsafe_surface",
        r"\bunsafe\b",
        "unsafe declaration or textual mention",
    ),
    ScanPattern(
        "v5.implemented_by",
        "compiler_override",
        r"\bimplemented_by\b",
        "implemented_by compiler override attribute or textual mention",
    ),
    ScanPattern(
        "v5.extern",
        "compiler_override",
        r"\bextern\b",
        "extern compiler binding attribute or textual mention",
    ),
    ScanPattern(
        "v5.csimp",
        "compiler_override",
        r"\bcsimp\b",
        "csimp compiler rewrite attribute or textual mention",
    ),
    ScanPattern(
        "v5.skip_kernel_tc",
        "checking_disabled",
        r"\bset_option\s+debug\.skipKernelTC\b",
        "set_option disabling kernel type checking",
    ),
    ScanPattern(
        "v5.bootstrap_option",
        "checking_disabled",
        r"\bset_option\s+bootstrap\.[A-Za-z_][A-Za-z0-9_.'-]*",
        "bootstrap set_option requiring trust review",
    ),
    ScanPattern(
        "v5.set_option",
        "option_inventory",
        r"\bset_option\s+[A-Za-z_][A-Za-z0-9_.'-]*",
        "all source set_option uses",
    ),
    ScanPattern(
        "v5.run_cmd",
        "elaboration_mutation",
        r"\brun_cmd\b",
        "elaboration-time run_cmd",
    ),
    ScanPattern(
        "v5.run_elab",
        "elaboration_mutation",
        r"\brun_elab\b",
        "elaboration-time run_elab",
    ),
    ScanPattern(
        "v5.eval",
        "elaboration_execution",
        r"(?<![A-Za-z0-9_'])#eval\b",
        "source #eval command",
    ),
    ScanPattern(
        "v5.initialize",
        "elaboration_mutation",
        r"\binitialize\b",
        "environment initialization command",
    ),
    ScanPattern(
        "v5.modifyEnv",
        "environment_mutation",
        r"\bmodifyEnv\b",
        "direct environment mutation API",
    ),
    ScanPattern(
        "v5.addDecl",
        "environment_mutation",
        r"\baddDecl\b",
        "direct declaration insertion API",
    ),
    ScanPattern(
        "v5.environment_add",
        "environment_mutation",
        r"\bEnvironment\.add\b",
        "direct Environment.add API",
    ),
    ScanPattern(
        "v5.partial_def",
        "definition_surface",
        r"\bpartial\s+def\b",
        "partial definition",
    ),
    ScanPattern(
        "v5.reducible",
        "definition_surface",
        r"\breducible\b",
        "reducible attribute or textual mention",
    ),
    ScanPattern(
        "v5.local_instance",
        "instance_surface",
        r"\blocal\s+instance\b",
        "local instance declaration",
    ),
    ScanPattern(
        "v5.fact",
        "instance_surface",
        r"\bFact\b",
        "Fact use requiring instance-context review",
    ),
    ScanPattern(
        "v5.macro_rules",
        "syntax_surface",
        r"\bmacro_rules\b",
        "macro_rules declaration",
    ),
    ScanPattern(
        "v5.macro",
        "syntax_surface",
        r"\bmacro\b",
        "macro declaration or textual mention",
    ),
    ScanPattern(
        "v5.elab_rules",
        "syntax_surface",
        r"\belab_rules\b",
        "elab_rules declaration",
    ),
    ScanPattern(
        "v5.elab",
        "syntax_surface",
        r"\belab\b",
        "custom elaborator declaration or textual mention",
    ),
    ScanPattern(
        "v5.notation",
        "syntax_surface",
        r"\bnotation\b",
        "notation declaration or textual mention",
    ),
    ScanPattern(
        "v5.syntax",
        "syntax_surface",
        r"\bsyntax\b",
        "custom syntax declaration or textual mention",
    ),
    ScanPattern(
        "v5.run_tac",
        "elaboration_execution",
        r"\brun_tac\b",
        "run_tac elaboration-time execution",
    ),
)
