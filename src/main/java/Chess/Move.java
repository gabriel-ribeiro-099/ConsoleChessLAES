package Chess;

public class Move {
    public final int x;
    public final int y;
    public final boolean firstMoveOnly;
    public final boolean onTakeOnly;

    /*@ public normal_behavior
      @     requires x >= 0;
      @     requires y >= 0;
      @     ensures this.x == x;
      @     ensures this.y == y;
      @     ensures this.firstMoveOnly == firstMoveOnly;
      @     ensures this.onTakeOnly == onTakeOnly;
      @ public exceptional_behavior
      @     requires x < 0 || y < 0;
      @     signals (IllegalArgumentException e) x < 0 || y < 0;
      @ signals_only IllegalArgumentException;
      @ pure
      @*/
    public Move(int x, int y, boolean firstMoveOnly, boolean onTakeOnly) {
        if (x < 0 || y < 0) {
            throw new IllegalArgumentException("Coordinates cannot be negative");
        }
        /*@ assert x >= 0 && y >= 0; @*/
        this.x = x;
        this.y = y;
        this.firstMoveOnly = firstMoveOnly;
        this.onTakeOnly = onTakeOnly;
    }
}
