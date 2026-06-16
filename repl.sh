#!/bin/bash
cd "$(dirname "$0")" || exit 1

echo "Stock REPL ready"
echo ""
echo "import Stock (Stock(..))"
echo ""
echo "Then try: :t Stock, :t Place, :i Ord Place"
echo ""

HOME=/tmp cabal repl examples
