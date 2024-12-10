package Chess.Pieces;

import Chess.ChessPiece;
import Chess.Move;

public class King extends ChessPiece{

	/*@
	@ requires color != null;
	@ requires color == PieceColor.White || color == PieceColor.Black;
	@ ensures getPieceType() == PieceType.King;
	@ ensures getMoves().length == 8;
	@ ensures hasRepeatableMoves() == false;
	@ also
	@ exceptional_behavior
	@ 	requires color == null || (color != PieceColor.White && color != PieceColor.Black);
	@ signals (IllegalArgumentException e) color == null || (color != PieceColor.White && color != PieceColor.Black);
	@*/
	public King(ChessPiece.PieceColor color){
		super(PieceType.King, color, validMoves(), false);
		//@ assert getPieceType() == PieceType.King;
	}
	/*@
	@ initially getPieceType() == PieceType.King;
	@ initially getMoves().length == 8;
	@ initially hasRepeatableMoves() == false;
	@ constraint getPieceType() == PieceType.King;
	@ constraint getMoves().length == 8;
	@ constraint hasRepeatableMoves() == false;
	@*/

	/*@
    @ ensures \result.length == 8;
    @ ensures (\forall int i; 0 <= i && i < \result.length; \result[i] != null);
    @ assignable \nothing;
    @ pure helper
    @*/
	private static Move[] validMoves(){
		return new Move[]{	new Move(1, 0, false, false), new Move(0, 1, false, false),
                        	new Move(-1, 0, false, false), new Move(0, -1, false, false),
                        	new Move(1, 1, false, false), new Move(1, -1, false, false),
                        	new Move(-1, 1, false, false), new Move(-1, -1, false, false)};
	}
}
