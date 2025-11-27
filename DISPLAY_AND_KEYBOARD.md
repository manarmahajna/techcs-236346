# Display and Keyboard Interface

**Based on**: [236346_Instructions_for_Display_and_Keyboard.pdf](file://236346_Instructions_for_Display_and_Keyboard.pdf)

## Display Adapter

### Video Memory Layout

**Base Address**: `0xa000`  
**Size**: 4096 words (0xa000 - 0xafff)  
**Display**: 256×256 pixels, monochrome (1 bit per pixel)  
**Organization**: Each word contains 16 pixels

```
Address = 0xa000 + (y * 16) + (x / 16)
Bit     = x % 16
```

### Display Scanning

**Auto-Scan**: Display adapter continuously scans lines
- Reads one line (16 words = 256 bits) per cycle
- Outputs to `vid_out` (256-bit register)
- Outputs line number to `vid_y` (0-255)
- Cycles indefinitely: 0 → 255 → 0 → ...

**Optimization**: Only modified lines are sent to UI (reduces I/O traffic)

### Memory Map

```
0xa000 ─────────┐
                │  Video Memory (256×256 pixels = 4096 words)
                │  Line 0: 0xa000 - 0xa00f (16 words)
                │  Line 1: 0xa010 - 0xa01f
                │  ...
                │  Line 255: 0xaff0 - 0xafff
0xb000 ─────────┤
                │  Kernel Code (new location!)
                │  (moved from 0xa800 to avoid overwriting video)
0xc000 ─────────┤
                │  GPIO
0xffff ─────────┘
```

**Important**: Kernel address changed from `0xa800` to `0xb000` to prevent video memory overlap!

---

## Keyboard Controller

### GPIO Protocol

**GPIO_IN**:
- Every 100ms (10 Hz), keyboard sends key code
- If no key pressed: sends `0x2d`
- Otherwise: sends key code

**Key Codes**:
```
Left:  0x4b
Up:    0x48
Right: 0x4d
Down:  0x50
None:  0x2d (also serves as timer tick)
```

### Reading Keys

**Polling** (from Phase 5):
```staml
wait(0) = 
    mem_peek 0xc001;    // Read sequence
    wait_aux

wait_aux(1) =
    if (mem_peek 0xc001) - $0
    then mem_peek 0xc000    // Sequence changed: return key
    else .wait_aux $0       // Tail call: keep polling
```

**Non-Blocking** (recommended for game):
```staml
try_read_key(1) =
    if key_available()
    then mem_peek 0xc000
    else $0    // Return default
```

---

## UI Application

### Setup

**Requirements**:
- Node.js and NPM
- NW.js (https://nwjs.io)

**Installation**:
```bash
npm i -g nw@sdk
```

**Windows/WSL Users**: Install NW.js on Windows, not WSL. Place project files where both can access.

### Launch

```bash
cd project-root
npm i
npm run download
npm start
```

**UI Window Opens** with:
- Screen area (256×256 black display)
- Settings: Simulation executable path, binary file path
- Controls: Start/Stop buttons
- Keyboard: Click screen to focus, use arrow keys

---

## Drawing Utilities

### Block-Based Drawing (8×8 blocks)

**From**: `sw/compiler/simple-progs.ir`

Utility functions for drawing 8×8 pixel blocks:

```staml
/* Draw 8x8 block at position (bx, by) with pattern */
draw_block(bx, by, pattern) = ...

/* Clear 8x8 block */
clear_block(bx, by) = ...

/* Draw filled square */
draw_square(x, y, size) = ...
```

**Block Coordinates**:
- Screen: 256×256 pixels = 32×32 blocks
- Block (bx, by): bx, by ∈ [0, 31]
- Pixel position: (bx*8, by*8)

---

## Snake Game Implementation Plan

### Step 1: Draw Single Block ✓
```staml
main(0) =
    draw_block 16 16 0xffff;    // Center of screen
    0
```

**Test**: Compile, run, see block at center

### Step 2: Arrow Key Response ✓
```staml
main(0) =
    let x = 16 in
    let y = 16 in
    draw_block x y 0xffff;
    game_loop x y

game_loop(x, y) =
    let key = wait() in
    clear_block x y;
    let (x', y') = move_position x y key in
    draw_block x' y';
    .game_loop x' y'    // Tail call!
```

### Step 3: FIFO for Snake Body ✓
```staml
/* Cyclic queue for snake positions */
snake_init(max_len) = ...
snake_push(queue, x, y) = ...
snake_pop(queue) = ...
snake_get(queue, index) = ...
```

**Data Structure**:
- Array: positions[MAX_LENGTH * 2] (x,y pairs)
- head: index of newest position
- tail: index of oldest position
- length: current snake length

### Step 4: Full Snake Game ✓

**Features**:
- Snake moves continuously
- Grows when eating food
- Collision detection (wall, self)
- Score tracking
- Game over screen

---

## Snake Game Specification

### Game State
```
State = {
    snake_positions: Array[(x,y)],  // FIFO queue
    snake_length: Int,
    direction: Direction,           // UP/DOWN/LEFT/RIGHT
    food_x: Int,
    food_y: Int,
    score: Int,
    game_over: Bool
}
```

### Game Loop
```staml
main(0) =
    let state = init_game() in
    .game_loop state

game_loop(state) =
    let key = try_read_key KEY_NONE in
    let state' = update_direction state key in
    let state'' = move_snake state' in
    let state''' = check_food state'' in
    render state''';
    if game_over state'''
    then show_game_over()
    else .game_loop state'''    // Tail call!
```

### Core Functions

**init_game()**: Initialize game state
- Snake at center: (16, 16)
- Length: 3
- Direction: RIGHT
- Random food position
- Score: 0

**update_direction(state, key)**: Change direction based on key
- Cannot reverse (UP→DOWN not allowed)
- Updates state.direction

**move_snake(state)**: Move snake one step
- Calculate new head position
- Push to FIFO
- If not eating, pop tail
- Return updated state

**check_food(state)**: Check if snake ate food
- If head == food: grow, new food, score++
- Return updated state

**check_collision(state)**: Check game over
- Head hits wall: game_over = true
- Head hits body: game_over = true

**render(state)**: Draw everything
- Clear old tail (if moved)
- Draw new head
- Draw food
- Update score display

---

## Properties to Verify

### Safety Properties

1. **Bounds Safety**:
   ```
   ∀i: 0 ≤ snake_x[i] < 32 ∧ 0 ≤ snake_y[i] < 32
   ```

2. **No Self-Overlap** (before collision):
   ```
   ∀i,j: i ≠ j ⇒ snake[i] ≠ snake[j]
   ```

3. **Food Placement**:
   ```
   ∀i: food_pos ≠ snake[i]
   ```

4. **Length Invariant**:
   ```
   length = initial_length + food_eaten
   ```

5. **Score Correctness**:
   ```
   score = food_eaten
   ```

### Liveness Properties

1. **Progress**: Snake moves every tick
2. **Termination**: Game eventually ends (collision or score limit)

---

## Implementation Tips

### 1. Start Simple
- Draw one block
- Make it move with keys
- Add trail (fixed length)

### 2. FIFO Implementation
```staml
/* Cyclic queue in memory */
QUEUE_BASE = 0x2000
QUEUE_MAX = 100

queue_init() =
    mem_poke QUEUE_BASE 0;      // head = 0
    mem_poke (QUEUE_BASE+1) 0;  // tail = 0
    mem_poke (QUEUE_BASE+2) 0   // length = 0

queue_push(x, y) =
    let head = mem_peek QUEUE_BASE in
    let len = mem_peek (QUEUE_BASE+2) in
    mem_poke (QUEUE_BASE+3 + head*2) x;
    mem_poke (QUEUE_BASE+3 + head*2 + 1) y;
    mem_poke QUEUE_BASE ((head+1) mod QUEUE_MAX);
    mem_poke (QUEUE_BASE+2) (len+1)

queue_pop() =
    let tail = mem_peek (QUEUE_BASE+1) in
    let len = mem_peek (QUEUE_BASE+2) in
    let x = mem_peek (QUEUE_BASE+3 + tail*2) in
    let y = mem_peek (QUEUE_BASE+3 + tail*2 + 1) in
    mem_poke (QUEUE_BASE+1) ((tail+1) mod QUEUE_MAX);
    mem_poke (QUEUE_BASE+2) (len-1);
    (x, y)
```

### 3. Collision Detection
```staml
check_wall_collision(x, y) =
    (x < 0) | (x >= 32) | (y < 0) | (y >= 32)

check_self_collision(head_x, head_y, queue) =
    // Check if head collides with any body segment
    check_queue_contains queue head_x head_y
```

### 4. Random Food Placement
```staml
/* Simple pseudo-random using score + timer */
random_food(state) =
    let seed = (state.score * 31 + timer()) mod 1024 in
    let x = seed mod 32 in
    let y = (seed / 32) mod 32 in
    if collides_with_snake(x, y, state)
    then random_food_retry state (seed+1)
    else (x, y)
```

---

## Testing

### Test 1: Display a Pattern
Create binary file with checkerboard:
```python
# Create 256x256 checkerboard pattern
pattern = []
for y in range(256):
    for x_word in range(16):
        word = 0
        for bit in range(16):
            if ((y // 8) + ((x_word*16 + bit) // 8)) % 2 == 0:
                word |= (1 << bit)
        pattern.append(word)

# Write to file
with open('checkerboard.bin', 'wb') as f:
    for word in pattern:
        f.write(word.to_bytes(2, 'little'))
```

Load via bootloader - should see checkerboard!

### Test 2: Single Block
```staml
main(0) =
    draw_block 16 16 0xffff;    // Center block
    wait();
    0
```

Should see white 8×8 block at center.

### Test 3: Moving Block
```staml
main(0) = moving_block 16 16

moving_block(x, y) =
    draw_block x y 0xffff;
    let key = wait() in
    clear_block x y;
    let (x', y') = 
        if key == 0x4b then (x-1, y)      // Left
        else if key == 0x4d then (x+1, y) // Right
        else if key == 0x48 then (x, y-1) // Up
        else if key == 0x50 then (x, y+1) // Down
        else (x, y) in
    .moving_block x' y'
```

---

## Files to Create

```
sw/game/
├── snake.staml              # Main Snake game
├── snake_utils.staml        # Drawing, FIFO, utilities
├── test_display.py          # Create test patterns
└── README.md

sw/compiler/
└── simple-progs.ir          # Block drawing utilities (existing)

Documentation/
├── DISPLAY_AND_KEYBOARD.md  # This file
└── SNAKE_GAME_COMPLETE.md   # Final documentation
```

---

## Resources

- **NW.js**: https://nwjs.io
- **Video Adapter**: `hw/cpu/periph.py` - `video_adapter()`
- **Keyboard**: `sw/verify/keyboard_controller.staml`
- **Drawing Utils**: `sw/compiler/simple-progs.ir`

---

## Next Steps

1. ✓ Understand display adapter
2. ✓ Update kernel address
3. ⬜ Test display with image
4. ⬜ Implement block drawing
5. ⬜ Build basic snake movement
6. ⬜ Add FIFO queue
7. ⬜ Complete Snake game
8. ⬜ Verify correctness

---

**Ready to build Snake!** 🐍🎮
