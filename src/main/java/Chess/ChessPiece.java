package Chess;

public abstract class ChessPiece {
    //@ spec_public
    private final PieceType type;

    //@ spec_public
    private final PieceColor color;

    //@ spec_public
    private final Move[] moves;

    //@ spec_public
    private final String name;

    //@ spec_public
    private final char charValue;

    //@ spec_public
    private final boolean repeatableMoves;

    /*@
    @ invariant !(type == null);
    @ invariant !(color == null);
    @ invariant moves != null && (\forall int i; 0 <= i && i < moves.length; moves[i] != null);
    @ invariant name != null && name.length() > 0;
    @ invariant charValue >= 'A' && charValue <= 'Z';
    @*/

    /*@
    @ protected normal_behavior
    @     requires type != null;
    @     requires color != null;
    @     requires moves != null;
    @     requires type.name() != null && !type.name().isEmpty();
    @     requires type.name().length() > 0;
    @     ensures this.type == type;
    @     ensures this.color == color;
    @     ensures this.moves == moves;
    @     ensures this.repeatableMoves == repeatableMoves;
    @     ensures this.name == type.name();
    @     ensures this.charValue == type.name().charAt(0);
    @ protected exceptional_behavior
    @     requires type.name() == null || type.name().isEmpty();
    @     signals (IllegalArgumentException e) type.name() == null || type.name().isEmpty();
    @ signals_only IllegalArgumentException;
    @ pure
    @*/
    protected ChessPiece(PieceType type, PieceColor color, Move[] moves, boolean repeatableMoves){
        if (type == null || type.name() == null || type.name().isEmpty()) {
            throw new IllegalArgumentException("Type or name cannot be null or empty");
        }

        String name = type.name();
        //@ assume name != null && name.length() > 0;

        char firstChar = name.charAt(0);
        //@ assume 0 <= 0 && 0 < name.length();

        if (firstChar < 'A' || firstChar > 'Z') {
            throw new IllegalArgumentException("First character of name must be between 'A' and 'Z'");
        }

        this.type = type;
        this.color = color;
        this.moves = moves;
        this.repeatableMoves = repeatableMoves;
        this.name = name;
        this.charValue = firstChar;
    }

    /*@
    @ invariant PieceType.Pawn != null;
    @ invariant PieceType.Rook != null;
    @ invariant PieceType.Knight != null;
    @ invariant PieceType.Bishop != null;
    @ invariant PieceType.Queen != null; 
    @ invariant PieceType.King != null; 
    @*/
    public enum PieceType {
        Pawn, Rook, Knight, Bishop, Queen, King
    }

    /*@
    @ invariant PieceColor.White != null;
    @ invariant PieceColor.Black != null;
    @*/
    public enum PieceColor {
        White, Black
    }

    /*@ 
    @ protected normal_behavior
    @   requires moves != null;
    @   ensures \result == moves; 
    @ pure
    @*/
    public Move[] getMoves() {
        return moves;
    }

    /*@ 
    @ protected normal_behavior
    @   requires name != null;
    @ pure
    @*/
    public String getName(){ return name; }

    /*@ 
    @ invariant color == PieceColor.White || color == PieceColor.Black;
    @ protected normal_behavior
    @   requires color != null;
    @ pure
    @*/
    public PieceColor getColor(){ return color; }

    /*@ 
    @ protected normal_behavior
    @ ensures \result == charValue; 
    @ pure
    @*/
    public char getCharValue() {
        return charValue;
    }

    /*@ 
    @ protected normal_behavior
    @   ensures \result == repeatableMoves; 
    @ assignable \nothing; 
    @ pure
    @*/
    public boolean hasRepeatableMoves() {
        return repeatableMoves;
    }

    /*@ 
    @ protected normal_behavior
    @   requires type != null;
    @ ensures \result == type;
    @ pure
    @*/
    public PieceType getPieceType() {
        // /*@ assert type != null; @*/
        return type;
    }

    /*@
    @ requires color != null; 
    @ ensures (color == PieceColor.Black) ==> (\result == PieceColor.White); 
    @ ensures (color == PieceColor.White) ==> (\result == PieceColor.Black); 
    @ assignable \nothing;
    @ pure
    @*/
    public static PieceColor opponent(PieceColor color) {
        /*@ assert color == PieceColor.Black || color == PieceColor.White; @*/
        return (color == PieceColor.Black) ? PieceColor.White : PieceColor.Black;
    }
}