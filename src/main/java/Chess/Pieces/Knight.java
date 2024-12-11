package Chess.Pieces;

import Chess.ChessPiece;
import Chess.Move;

public class Knight extends ChessPiece{

	/*@
	@ requires color != null;
	@ requires color == PieceColor.White || color == PieceColor.Black;
	@ ensures getPieceType() == PieceType.Knight;
	@ ensures getMoves().length == 12;
	@ ensures hasRepeatableMoves() == false;
	@ also
	@ exceptional_behavior
	@ 	requires color == null || (color != PieceColor.White && color != PieceColor.Black);
	@ signals (IllegalArgumentException e) color == null || (color != PieceColor.White && color != PieceColor.Black);
	@*/
	public Knight(ChessPiece.PieceColor color){
		super(PieceType.Knight, color, validMoves(), false);
		//@ assert getPieceType() == PieceType.Knight;
	}
	/*@
	@ initially getPieceType() == PieceType.Knight;
	@ initially getMoves().length == 12;
	@ initially hasRepeatableMoves() == false;
	@ constraint getPieceType() == PieceType.Knight;
	@ constraint getMoves().length == 12;
	@ constraint hasRepeatableMoves() == false;
	@*/

	/*@
    @ ensures \result.length == 12;
    @ ensures (\forall int i; 0 <= i && i < \result.length; \result[i] != null);
    @ assignable \nothing;
    @ pure helper
    @*/
	private static Move[] validMoves(){
		return new Move[]{	new Move(2, 1, false, false), new Move(1, 2, false, false),
	                    	new Move(2, -1, false, false), new Move(-1, 2, false, false),
	                        new Move(2, -1, false, false), new Move(-1, 2, false, false),
	                        new Move(-2, 1, false, false), new Move(1, -2, false, false),
	                        new Move(-2, -1, false, false), new Move(-1, -2, false, false),
	                        new Move(-2, -1, false, false), new Move(-1, -2, false, false)};
	}
}
