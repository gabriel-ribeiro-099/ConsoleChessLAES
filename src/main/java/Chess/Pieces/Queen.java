package Chess.Pieces;

import Chess.ChessPiece;
import Chess.Move;

public class Queen extends ChessPiece{

	/*@
	@ requires color != null;
	@ requires color == PieceColor.White || color == PieceColor.Black;
	@ ensures getPieceType() == PieceType.Queen;
	@ ensures getMoves().length == 8;
	@ ensures hasRepeatableMoves() == true;
	@ also
	@ exceptional_behavior
	@ 	requires color == null || (color != PieceColor.White && color != PieceColor.Black);
	@ signals (IllegalArgumentException e) color == null || (color != PieceColor.White && color != PieceColor.Black);
	@*/
	public Queen(ChessPiece.PieceColor color){
		super(PieceType.Queen, color, validMoves(), true);
		//@ assert getPieceType() == PieceType.Queen;
	}
	/*@
	@ initially getPieceType() == PieceType.Queen;
	@ initially getMoves().length == 8;
	@ initially hasRepeatableMoves() == true;
	@ constraint getPieceType() == PieceType.Queen;
	@ constraint getMoves().length == 8;
	@ constraint hasRepeatableMoves() == true;
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