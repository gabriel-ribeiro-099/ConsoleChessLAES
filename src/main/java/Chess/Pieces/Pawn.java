package Chess.Pieces;

import Chess.ChessPiece;
import Chess.Move;

public class Pawn extends ChessPiece {

    /*@
	@ requires color != null;
	@ requires color == PieceColor.White || color == PieceColor.Black;
	@ ensures getPieceType() == PieceType.Pawn;
	@ ensures getMoves().length == 4;
	@ ensures hasRepeatableMoves() == false;
	@ also
	@ exceptional_behavior
	@ 	requires color == null || (color != PieceColor.White && color != PieceColor.Black);
	@ signals (IllegalArgumentException e) color == null || (color != PieceColor.White && color != PieceColor.Black);
	@*/
	public Pawn(PieceColor color){
		super(PieceType.Pawn, color, validMoves(color), false);
        //@ assert getPieceType() == PieceType.Pawn;
	}
    /*@
	@ initially getPieceType() == PieceType.Pawn;
	@ initially getMoves().length == 4;
	@ initially hasRepeatableMoves() == false;
	@ constraint getPieceType() == PieceType.Pawn;
	@ constraint getMoves().length == 4;
	@ constraint hasRepeatableMoves() == false;
	@*/

    /*@
    @ requires color != null;
    @ requires color == PieceColor.Black || color == PieceColor.White;
    @ ensures \result.length == 4;
    @ ensures (\forall int i; 0 <= i && i < \result.length; \result[i] != null);
    @ assignable \nothing;
    @ pure helper
    @*/
	private static Move[] validMoves(PieceColor color){
        if (color == PieceColor.Black){
            return new Move[]{new Move(0, 1, false, false), new Move(0, 2, true, false),
                              new Move(1, 1, false, true), new Move(-1, 1, false, true)};
        } else {
            return new Move[]{new Move(0, -1, false, false), new Move(0, -2, true, false),
                              new Move(1, -1, false, true), new Move(-1, -1, false, true)};
        }
	}
}
