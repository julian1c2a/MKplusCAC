#!/bin/bash
# git-lock.bash — File locking system for Lean 4 projects
# Prevents accidental edits to completed modules via git pre-commit hook.
#
# Usage:
#   bash git-lock.bash lock   MKplus/Module.lean   # lock file
#   bash git-lock.bash unlock MKplus/Module.lean   # unlock file
#   bash git-lock.bash list                             # show locked files
#   bash git-lock.bash init                             # install git hook
#
# Protocol:
#   - At session start: run 'list', unlock only the file you need
#   - When switching files: lock current before unlocking next
#   - At session end: lock all modified files, commit locked_files.txt

LOCK_LIST="locked_files.txt"

show_help() {
    echo "Usage: bash git-lock.bash [command] [file]"
    echo "Commands:"
    echo "  lock   <file>  : Lock file (add to list, remove write permission)"
    echo "  unlock <file>  : Unlock file (remove from list, restore write permission)"
    echo "  list           : Show currently locked files"
    echo "  init           : Install pre-commit hook"
}

if [ $# -eq 0 ]; then
    show_help
    exit 1
fi

COMMAND=$1
FILE=$2

touch "$LOCK_LIST"

case $COMMAND in
    lock)
        if [ -z "$FILE" ]; then
            chmod a-w "$LOCK_LIST"
            echo "🔒 Permisos de escritura eliminados para '$LOCK_LIST'."
            exit 0
        fi
        if [ ! -f "$FILE" ]; then echo "Error: El archivo '$FILE' no existe."; exit 1; fi
        if ! grep -Fxq "$FILE" "$LOCK_LIST"; then
            echo "$FILE" >> "$LOCK_LIST"
            echo "Añadido '$FILE' a $LOCK_LIST."
        else
            echo "'$FILE' ya estaba en la lista."
        fi
        chmod a-w "$FILE"
        echo "🔒 Permisos de escritura eliminados para '$FILE'."
        ;;

    unlock)
        if [ -z "$FILE" ]; then
            chmod u+w "$LOCK_LIST"
            echo "🔓 Permisos de escritura restaurados para '$LOCK_LIST'."
            exit 0
        fi
        if grep -Fxq "$FILE" "$LOCK_LIST"; then
            grep -Fv "$FILE" "$LOCK_LIST" > "${LOCK_LIST}.tmp" && mv "${LOCK_LIST}.tmp" "$LOCK_LIST"
            echo "Eliminado '$FILE' de $LOCK_LIST."
        else
            echo "Advertencia: '$FILE' no estaba en la lista de bloqueados."
        fi
        if [ -f "$FILE" ]; then
            chmod u+w "$FILE"
            echo "🔓 Permisos de escritura restaurados para '$FILE'."
        fi
        ;;

    list)
        echo "=== Archivos Bloqueados (en $LOCK_LIST) ==="
        if [ -s "$LOCK_LIST" ]; then
            cat "$LOCK_LIST"
        else
            echo "(Ninguno)"
        fi
        ;;

    init)
        touch "$LOCK_LIST"
        HOOK_DIR=".git/hooks"
        HOOK_FILE="$HOOK_DIR/pre-commit"
        if [ ! -d ".git" ]; then
            echo "Error: Not in a git repository root."
            exit 1
        fi
        echo "Installing hook at $HOOK_FILE..."
        cat > "$HOOK_FILE" << 'HOOKEOF'
#!/bin/bash
# Pre-commit hook: blocks commits touching locked files, warns about new sorry

LOCK_LIST="locked_files.txt"
STAGED_FILES=$(git diff --cached --name-only)
ERROR=0

# --- Check 1: Locked files ---
if [ -f "$LOCK_LIST" ]; then
    while IFS= read -r LOCKED_FILE; do
        [ -z "$LOCKED_FILE" ] && continue
        if echo "$STAGED_FILES" | grep -Fqx "$LOCKED_FILE"; then
            echo "❌ LOCKED: $LOCKED_FILE"
            echo "   Unlock first: bash git-lock.bash unlock $LOCKED_FILE"
            ERROR=1
        fi
    done < "$LOCK_LIST"
fi

# --- Check 2: New sorry statements (warning only) ---
SORRY_COUNT=0
for F in $STAGED_FILES; do
    if [[ "$F" == *.lean ]] && [ -f "$F" ]; then
        N=$(grep -c 'sorry' "$F" 2>/dev/null || true)
        N="${N//[^0-9]/}"   # strip any non-numeric chars (MSYS safety)
        N="${N:-0}"
        if [ "$N" -gt 0 ] 2>/dev/null; then
            echo "⚠️  WARNING: $N sorry in $F"
            SORRY_COUNT=$((SORRY_COUNT + N))
        fi
    fi
done
[ "$SORRY_COUNT" -gt 0 ] && echo "   Total sorry statements in staged files: $SORRY_COUNT"

if [ $ERROR -eq 1 ]; then
    exit 1
fi
exit 0
HOOKEOF
        chmod +x "$HOOK_FILE"
        echo "✅ Lock system initialized. Pre-commit hook installed."
        ;;

    *)
        show_help
        exit 1
        ;;
esac
