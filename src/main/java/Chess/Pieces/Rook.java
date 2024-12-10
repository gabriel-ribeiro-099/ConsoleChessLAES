package Chess.Pieces;

import Chess.ChessPiece;
import Chess.Move;

public class Rook extends ChessPiece {

	/*@
	@ requires color == PieceColor.White || color == PieceColor.Black;
	@ ensures getPieceType() == PieceType.Rook;
	@ ensures getMoves().length == 4;
	@ ensures hasRepeatableMoves() == true;
	@ exceptional_behavior
	@ 	requires color != PieceColor.White && color != PieceColor.Black;
	@ signals (IllegalArgumentException e) color != PieceColor.White && color != PieceColor.Black;
	@*/
	public Rook(PieceColor color) {
		super(PieceType.Rook, color, validMoves(), true);
		//@ assert getPieceType() == PieceType.Rook;
	}
	/*@
	@ initially getPieceType() == PieceType.Rook;
	@ initially getMoves().length == 4;
	@ initially hasRepeatableMoves() == true;
	@ constraint getPieceType() == PieceType.Rook;
	@ constraint getMoves().length == 4;
	@ constraint hasRepeatableMoves() == true;
	@*/




    /*@
      @ ensures \result.length == 4;
      @ ensures (\forall int i; 0 <= i && i < \result.length; \result[i] != null);
	  @ assignable \nothing;
	  @ pure helper
      @*/
    private static Move[] validMoves() {
        return new Move[] {
            new Move(1, 0, false, false),
            new Move(0, 1, false, false),
            new Move(-1, 0, false, false),
            new Move(0, -1, false, false)
        };
    }
}
