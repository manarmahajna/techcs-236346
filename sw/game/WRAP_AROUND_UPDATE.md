# 🐍 Snake Game Update: Wrap-Around Edges!

## What Changed

The Snake game now has **wrap-around edges** (toroidal topology)!

### Before:
- Snake hits wall → Game Over 💥
- Screen has hard boundaries

### After:
- Snake goes off top → Appears at bottom ✨
- Snake goes off bottom → Appears at top ✨
- Snake goes off left → Appears at right ✨
- Snake goes off right → Appears at left ✨

## How It Works

### In `snake_utils.staml`:

```staml
/* Wrap coordinates to opposite side */
wrap_x(x) =
    if x < 0 then SCREEN_BLOCKS - 1
    else if x >= SCREEN_BLOCKS then 0
    else x

wrap_y(y) =
    if y < 0 then SCREEN_BLOCKS - 1
    else if y >= SCREEN_BLOCKS then 0
    else y

/* Calculate new position (with wrap-around) */
next_position(x, y, dir) =
    let (new_x, new_y) = 
        if dir == DIR_UP then (x, y - 1)
        else if dir == DIR_DOWN then (x, y + 1)
        else if dir == DIR_LEFT then (x - 1, y)
        else (x + 1, y)
    in
    wrap_position new_x new_y
```

### In `snake.staml`:

```staml
move_snake(0) =
    let (new_x, new_y) = next_position head_x head_y dir in
    
    // Only check self collision (no walls!)
    if collides_with_snake new_x new_y
    then mem_poke STATE_GAME_OVER 1
    else ...
```

## Updated Properties

### Still Verified ✅
1. **Position Safety**: After wrapping, all positions are in [0, 31]
2. **No Self-Overlap**: Snake body never overlaps itself
3. **Food Placement**: Food never on snake
4. **Length Correctness**: `length = initial + eaten`
5. **Score Correctness**: `score = eaten`
6. **Queue Integrity**: FIFO works correctly
7. **Movement Progress**: Snake always moves

### Changed ✅
- ~~Wall Collision~~ → **Wrap-around** (no wall collisions!)
- Only way to lose: Hit yourself

## Gameplay Impact

**Easier**:
- Can't die from walls
- More forgiving for beginners
- Can escape tight situations

**Harder**:
- Snake gets longer → harder to avoid self
- Wrapping can be confusing at first
- Need better spatial awareness

**More Fun**:
- Classic arcade feel (like Pac-Man)
- Longer gameplay sessions
- Can reach higher scores!

## Try It Now!

```bash
cd /mswg/projects/fw/fw_ver/potato/workspace/project/techcs-236346-master/sw/game
python3 demo_snake.py
```

Watch the snake wrap around the edges! 🐍✨

---

**Updated**: November 27, 2025  
**Feature**: Toroidal topology (wrap-around)  
**Status**: Implemented and tested ✅
