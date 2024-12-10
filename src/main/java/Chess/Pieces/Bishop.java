package Chess.Pieces;

import Chess.ChessPiece;
import Chess.Move;

public class Bishop extends ChessPiece {

	/*@
	@ requires color != null;
	@ requires color == PieceColor.White || color == PieceColor.Black;
	@ ensures getPieceType() == PieceType.Bishop;
	@ ensures getMoves().length == 4;
	@ ensures hasRepeatableMoves() == true;
	@ also
	@ exceptional_behavior
	@ 	requires color == null || (color != PieceColor.White && color != PieceColor.Black);
	@ signals (IllegalArgumentException e) color == null || (color != PieceColor.White && color != PieceColor.Black);
	@*/
	public Bishop(PieceColor color){
		super(PieceType.Bishop, color, validMoves(), true);
		//@ assert getPieceType() == PieceType.Bishop;
	}
	/*@
	@ initially getPieceType() == PieceType.Bishop;
	@ initially getMoves().length == 4;
	@ initially hasRepeatableMoves() == true;
	@ constraint getPieceType() == PieceType.Bishop;
	@ constraint getMoves().length == 4;
	@ constraint hasRepeatableMoves() == true;
	@*/


	/*@
    @ ensures \result.length == 4;
    @ ensures (\forall int i; 0 <= i && i < \result.length; \result[i] != null);
    @ assignable \nothing;
    @ pure helper
    @*/
	private static Move[] validMoves(){
		return	new Move[]{	new Move(1, 1, false, false), new Move(1, -1, false, false),
	                        new Move(-1, 1, false, false), new Move(-1, -1, false, false)};
	}
}
