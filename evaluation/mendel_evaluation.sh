#!/usr/bin/env bash

set -euo pipefail

# Folder in which the script is contained
SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

# Root folder of the project
ROOT_DIR="$SCRIPT_DIR/.."

# Evaluation folders
CLIENTS_DIR="$ROOT_DIR/prusti-tests/tests/verify_safe_clients/fail/clients"
LIBRARIES_DIR="$ROOT_DIR/prusti-tests/tests/verify_safe_clients/fail/libraries"

CLIENTS_FILES=( \
    "arc.rs" "arc_rwlock.rs" "atomic.rs" "cell.rs" "mutex.rs" "rc.rs" "refcell.rs" \
    "unsafecell.rs" "box.rs" "mutex_inv.rs" "verus_cell.rs" "verus_ptr.rs" \
)
LIBRARIES_FILES=( \
    "lib_unsafecell.rs" "lib_rc.rs" "lib_arc.rs" "lib_cell.rs" "lib_refcell.rs" \
    "lib_refcell_ref.rs" "lib_refcell_refmut.rs" "lib_atomic.rs" "lib_mutex.rs" \
    "lib_mutex_guard.rs" "lib_rwlock.rs" "lib_rwlock_readguard.rs" "lib_rwlock_writeguard.rs" \
    "lib_box.rs" "lib_option.rs" "lib_result.rs" "lib_controlflow.rs" \
    "lib_mutex_inv.rs" "lib_verus_cell.rs" "lib_verus_ptr.rs"
)

# Measure number of lines for each file in the evaluation folders
for DIR in "$CLIENTS_DIR" "$LIBRARIES_DIR"; do
    DIRNAME="$(basename "$DIR")"
    echo "=== Content of $DIRNAME ==="

    if [ "$DIRNAME" = "clients" ]; then
        printf "%-30s %5s %5s %5s %5s\n" "File"      "Lines"      "Contr"           "Asser"       "Incom"
        FILES=("${CLIENTS_FILES[@]}")
    else
        printf "%-30s %5s %5s %5s %5s %5s %5s\n" "File"      "Lines"      "Impur"             "Pure"            "Ghost"            "Capab"             "Contr"
        FILES=("${LIBRARIES_FILES[@]}")
    fi

    for FILENAME in "${FILES[@]}"; do
        FILE="$DIR/$FILENAME"

        # Content of the file, optionally ignoring what before "EVALUATION:IGNOREBEFORE" or after "EVALUATION:IGNOREAFTER"
        CONTENT="$(sed -ne '1,/EVALUATION:IGNOREBEFORE/d; /EVALUATION:IGNOREAFTER/,$d; p' "$FILE")"

        # Count number of lines of code, excluding empty lines and comment lines
        TOT_LINES="$(echo -n "$CONTENT" | grep -v -e '^\s*$' -e '^\s*//'  -e '^\s*/\*[^*]*\*/\s*$' | wc -l || true)"

        # Count number of lines of contracts
        CONTRACT_LINES="$(echo -n "$CONTENT" | awk '/#\[(requires|ensures|pure)/,/\]/{ print }' | wc -l || true)"

        # Extract assertions
        ASSERTIONS="$(echo -n "$CONTENT" | grep 'assert!(' || true)"

        # Count number of non-incompleteness assertions
        NUM_CHECKS="$(echo -n "$ASSERTIONS" | grep -vi 'incompleteness' | wc -l || true)"

        # Count number of incompleteness checks
        NUM_INCOMLETENESS_CHECKS="$(echo -n "$ASSERTIONS" | grep -i 'incompleteness' | wc -l || true)"

        # Count number of capabilities
        NUM_CAPABILITIES="$(echo -n "$CONTENT" | grep '#\[capable(' | wc -l || true)"

        # Extract functions
        FUNCTIONS="$(
            ( echo "{" ; echo -n "{ $CONTENT" | grep '\(\[\(pure\|ghost\|trusted\)\|fn \)' \
                | sed 's/^.*\[pure.*$/pure /; s/^.*\[ghost.*$/ghost /; s/^.*\[trusted.*$/trusted /' \
                | sed 's/^.*\bfn \([a-z0-9_]*\).*\;.*$/trusted function \1 }\n{/' \
                | sed 's/^.*fn \([a-z0-9_]*\).*{.*$/function \1 }\n{/'
            ) | head -n -1 | tr '\n' ' ' | grep -oe '{[^}]*}' || true
        )"

        # Count number of ghost functions
        GHOST_FUNCTIONS="$(echo -n "$FUNCTIONS" | grep 'ghost' | wc -l || true)"

        # Count number of pure functions
        PURE_FUNCTIONS="$(echo -n "$FUNCTIONS" | grep -v 'ghost' | grep 'pure' | wc -l || true)"

        # Count number of impure functions
        IMPURE_FUNCTIONS="$(echo -n "$FUNCTIONS" | grep -v 'ghost' | grep -v 'pure' | wc -l || true)"

        # Count number of trusted functions
        # Warning: this miscounts #[extern_specs] methods; count them manually!
        #TRUSTED_FUNCTIONS="$(echo -n "$FUNCTIONS" | grep 'trusted' | wc -l || true)"

        # Count number of verified functions
        # Warning: this miscounts #[extern_specs] methods; count them manually!
        #VERIFIED_FUNCTIONS="$(echo -n "$FUNCTIONS" | grep -v 'trusted' | wc -l || true)"

        # Print findings in a table
        if [ "$DIRNAME" = "clients" ]; then
            printf "%-30s %5d %5d %5d %5d\n" "$FILENAME" "$TOT_LINES" "$CONTRACT_LINES" "$NUM_CHECKS" "$NUM_INCOMLETENESS_CHECKS"
        else
            printf "%-30s %5d %5d %5d %5d %5d %5d\n" "$FILENAME" "$TOT_LINES" "$IMPURE_FUNCTIONS" "$PURE_FUNCTIONS" "$GHOST_FUNCTIONS" "$NUM_CAPABILITIES" "$CONTRACT_LINES"
        fi
    done
done
