#!/bin/bash
# Quick way to see the Snake game in action!

echo ""
echo "╔════════════════════════════════════════════════════════════════╗"
echo "║                                                                ║"
echo "║                  🐍 SNAKE GAME - QUICK DEMO 🐍                 ║"
echo "║                                                                ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""
echo "Choose an option:"
echo ""
echo "  1) Watch automated Snake demo (text-based)"
echo "  2) Verify game correctness (formal verification)"
echo "  3) View game source code"
echo "  4) Read full documentation"
echo ""
read -p "Enter choice (1-4): " choice

case $choice in
    1)
        echo ""
        echo "Starting Snake demo..."
        cd sw/game && python3 demo_snake.py
        ;;
    2)
        echo ""
        echo "Running formal verification..."
        cd sw/game && python3 verify_snake.py
        ;;
    3)
        echo ""
        echo "=== Snake Game Source Code ==="
        echo ""
        head -100 sw/game/snake.staml
        echo ""
        echo "(showing first 100 lines)"
        ;;
    4)
        echo ""
        cat PLAY_SNAKE.md | head -100
        ;;
    *)
        echo "Invalid choice"
        ;;
esac
