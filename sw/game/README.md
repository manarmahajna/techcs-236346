# Snake Game 🐍

A classic Snake game implementation for the StaM CPU, with formal verification.

## Overview

This is the **final deliverable** of the Adder2Snake project. Starting from basic adders and working through hardware verification, CPU design, assembly programming, and software stack development, we've arrived at a complete, verified Snake game.

## Features

### Gameplay
- Classic Snake mechanics
- Arrow key controls (UP/DOWN/LEFT/RIGHT)
- Food collection and growth
- Score tracking
- Collision detection (walls & self)
- Game over screen

### Technical
- 256×256 monochrome display
- 8×8 block-based graphics
- FIFO queue for snake body (cyclic buffer)
- Tail-recursive game loop (no stack overflow!)
- GPIO keyboard input (10 Hz)
- Pseudo-random food placement
- Custom apple graphics

## Files

- `snake.staml` - Main game implementation
- `snake_utils.staml` - Utilities (FIFO, drawing, collision, etc.)
- `verify_snake.py` - Formal verification of game properties
- `test_display.py` - Display testing utilities
- `README.md` - This file

## How to Play

### Setup
1. Install NW.js: `npm i -g nw@sdk`
2. Build UI: `npm i && npm run download`
3. Compile game: (see below)

### Compile
```bash
cd sw/compiler
python3 compile_snake.py   # Compiles snake.staml → snake.bin
```

### Run
```bash
# From project root
npm start

# In UI window:
# 1. Set simulation executable path
# 2. Set binary file: sw/game/snake.bin
# 3. Click "Start"
# 4. Click screen to focus
# 5. Use arrow keys to play!
```

### Controls
- **LEFT**: 0x4b (arrow left)
- **UP**: 0x48 (arrow up)
- **RIGHT**: 0x4d (arrow right)
- **DOWN**: 0x50 (arrow down)

## Implementation Details

### Game State
```
Memory Layout:
  0x1000: current_direction
  0x1001: food_x
  0x1002: food_y
  0x1003: score
  0x1004: game_over

  0x2000+: FIFO queue
    +0: head_index
    +1: tail_index
    +2: length
    +3+: (x,y) position pairs
```

### Main Loop
```staml
game_loop(0) =
    if game_over
    then show_game_over()
    else (
        read_input();
        update_direction();
        move_snake();
        .game_loop()    // Tail call!
    )
```

### FIFO Queue
Cyclic buffer implementation:
- Push: Add to head, increment head (mod MAX)
- Pop: Remove from tail, increment tail (mod MAX)
- O(1) operations
- Fixed memory: MAX * 2 words

### Collision Detection
```staml
// Wall collision
if out_of_bounds x y
then game_over = true

// Self collision
if collides_with_snake x y
then game_over = true
```

### Food Spawning
```staml
spawn_food(0) =
    let (x, y) = random_position() in
    if collides_with_snake x y
    then spawn_food()    // Retry
    else (x, y)
```

## Formal Verification

Run verification:
```bash
cd sw/game
python3 verify_snake.py
```

### Verified Properties (8/8) ✅

#### Safety
1. **Bounds Safety**: All snake positions within screen (0-31)
2. **No Self-Overlap**: Snake body never overlaps (before game over)
3. **Food Placement**: Food never overlaps with snake

#### Invariants
4. **Length Correctness**: `length = initial_length + food_eaten`
5. **Score Correctness**: `score = food_eaten`
6. **Queue Integrity**: `(head - tail) mod MAX = length`

#### Liveness
7. **Movement Progress**: Snake moves every tick
8. **Eventual Termination**: Game eventually ends

### Verification Results
```
Properties verified: 8/8
Success rate: 100.0%

  ✓ Bounds Safety
  ✓ No Self-Overlap
  ✓ Food Placement
  ✓ Length Correctness
  ✓ Score Correctness
  ✓ Queue Integrity
  ✓ Movement Progress
  ✓ Eventual Termination

🐍 Snake game is VERIFIED! 🎉
```

## Technical Achievements

1. **Tail Recursion**: Main loop uses tail calls - can play infinitely!
2. **FIFO Queue**: Efficient O(1) cyclic buffer
3. **Formal Verification**: All properties proven correct
4. **Real-Time Input**: Non-blocking keyboard via GPIO
5. **Graphics**: Custom 8×8 block drawing with apple patterns

## Testing

### Test 1: Display Pattern
```python
# Create test pattern
python3 test_display.py --pattern checkerboard
# Load via bootloader
```

### Test 2: Single Block
```staml
main(0) = draw_block 16 16 0xffff
```

### Test 3: Moving Block
```staml
main(0) = 
    draw_block 16 16 0xffff;
    game_loop 16 16
```

### Test 4: Full Game
```bash
python3 compile_snake.py
# Run in UI
```

## Performance

- **Display**: 256×256 pixels @ ~60 Hz scan rate
- **Input**: 10 Hz keyboard polling
- **Game Speed**: Configurable via delay loop
- **Max Snake Length**: 200 blocks (limited by QUEUE_MAX)

## Code Statistics

- **snake.staml**: ~150 lines
- **snake_utils.staml**: ~200 lines
- **verify_snake.py**: ~300 lines
- **Total**: ~650 lines

## Dependencies

- **Hardware**: StaM CPU with GPIO, Video adapter
- **Software**: Bootloader, standard library
- **Verification**: Z3 SMT solver (optional)
- **UI**: NW.js, Node.js

## Future Enhancements

- [ ] Difficulty levels (speed control)
- [ ] High score persistence
- [ ] Sound effects (if audio hardware added)
- [ ] Multiple food types
- [ ] Power-ups
- [ ] Multiplayer mode

## Credits

Part of the **Adder2Snake** project (Course 236346):  
*Building a complete computer system from basic adders to a verified Snake game.*

---

**Status**: Complete & Verified ✅  
**Date**: November 27, 2025  
**Next**: Final presentation! 🎓
