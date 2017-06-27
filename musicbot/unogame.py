import os
import re
import discord
import asyncio
import traceback
# honestly these imports are just in case i need them
import random


class The_Game:
    def __init__(self, bot, GameServer, GameChannel, GameAuthor):
        self.boundserver = GameServer
        self.chan = GameChannel             #access name with self.chan.name
        self.auth = GameAuthor              #mostly just to keep track of who made the game
        self.players = [GameAuthor]         #required for most functions    THE MAX AMOUNT OF PLAYERS IS 10 DUE TO THE CONSTRAINT OF THERE BEING FINITE CARDS, 7 PER PERSON
        self.gameLaunchedFlag = False       #to keep track of if the game has started (halting most commands)
        self.reverseFlag = True             #True = Normal Play, in the order of the players array.
        #self.passFlag = False            #to allow players to pass based on drawing (may not need to be used)
        #self.tempFlag = True             #this was a placeholder for stopping people from making another game but might not be necessary
        self.drawCounter = 0                #to keep track of the number of draws to force or allow a pass
        #self.quitFlag = True             #this was a placeholder to keep track if the game existed (for using most commands)
        self.botFlag = False                #to keep track of whether or not the bot is playing
        self.currentTurn = 0                #to keep track of the current turn position in the array of players
        #self.numberOfPlayers = 0         #number of players (replaceable by len(self.players)-1, used to make sure the turns didnt go out of order
        self.gameCards = ["1 b", "2 b", "3 b", "4 b", "5 b", "6 b", "7 b", "8 b", "9 b", "1 y", "2 y", "3 y", "4 y", "5 y", "6 y", "7 y", "8 y", "9 y", "1 g", "2 g", "3 g", "4 g", "5 g", "6 g", "7 g", "8 g", "9 g", "1 r", "2 r", "3 r", "4 r", "5 r", "6 r", "7 r", "8 r", "9 r", "1 b", "2 b", "3 b", "4 b", "5 b", "6 b", "7 b", "8 b", "9 b", "0 b", "1 y", "2 y", "3 y", "4 y", "5 y", "6 y", "7 y", "8 y", "9 y", "0 y", "1 g", "2 g", "3 g", "4 g", "5 g", "6 g", "7 g", "8 g", "9 g", "0 g", "1 r", "2 r", "3 r", "4 r", "5 r", "6 r", "7 r", "8 r", "9 r", "0 r", "wd4", "wd4", "wd4", "wd4", "d2 r", "d2 r", "d2 y", "d2 y", "d2 g", "d2 g", "d2 b", "d2 b", "s r", "s r", "s g", "s g", "s b", "s b", "s y", "s y", "r r", "r r", "r y", "r y", "r b", "r b", "r g", "r g", "w", "w", "w", "w"]
        random.shuffle(self.gameCards)
        self.playerLeftText = None          #a holder checked very quickly after it is set to determine the behavior of the next turn
        self.discardedCards = []
        self.playerCards = {GameAuthor.id:self.card_Gen(7)}      #a dictionary of all players by ID and their cards
        self.topCard = self.card_Gen(1)     #this is actually an array of a single string
        
        if len(self.topCard[0].split()) == 1:       #for the oddball case that we get a wild card for first drawn card
            while len(self.topCard[0].split()) == 1:
                self.gameCards.append(self.topCard[0])
                self.topCard = self.card_Gen(1)
                
        self.botDrew = False
        
        self.messageHolder = None           #this will be assigned very quickly after the object is made, but not yet
        self.colorURL = self.get_color_url(self.topCard[0].split())
        self.cleanupCounter = 0             #upon reaching 10 this will delete and repost the main message via function. it increments for every noncommand.
        
        self.loop = bot.loop                #to be able to async with the bot
        self.bot = bot                      #to be able to mess with the self.messageHolder
        self.latestMessage = None
        self.alternateMessage = None
        



    def get_color_url(self, cardArr): #this assumes that the card has already been put into simplest terms
        ''' Provides a color URL based on the color of the card given (card must be in array form, [value,color]'''
        
        if cardArr[1].lower() in ["r", "red"]:
            return "http://i.imgur.com/ucyL7Qs.png"
        if cardArr[1].lower() in ["y", "yellow"]:
            return "http://i.imgur.com/kiSKSRp.png"
        if cardArr[1].lower() in ["b", "blue"]:
            return "http://i.imgur.com/r6iBRKF.png"
        if cardArr[1].lower() in ["g", "green"]:
            return "http://i.imgur.com/G1ZiS1G.png"
        
        
    def card_Gen(self, NumberOfCards):
        ''' Generates some cards to deal. It removes cards from the deck, taking from the discarded pile if needed'''

        if len(self.gameCards) < NumberOfCards:
            self.gameCards = self.gameCards + self.discardedCards
            random.shuffle(self.gameCards)
        givencards = []
        for _ in range(NumberOfCards):
            givencards.append(self.gameCards.pop(random.randrange(0,len(self.gameCards))))
        return givencards

        
    def card_Checker(self, cardArr):    #it's expected by this point that the card given is in the form of an array
        ''' Checks to see if a card, given as an array ["Value", "Color"], is legitimate'''
    
        if cardArr[0].lower() in ["w", "wd4", "s", "r", "d2", "wild", "wilddraw4", "draw4", "skip", "reverse", "draw2"]: 
            if cardArr[1].lower() in ["r", "g", "b", "y", "red", "green", "blue", "yellow"]:
                return True
        if cardArr[0].lower() in ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]:
            if cardArr[1].lower() in ["r", "g", "b", "y", "red", "green", "blue", "yellow"]:
                return True
        return False
    
    
    def card_Converter(self, cardArr, ColorOnly=False):  #it's expected by this point that the card given is in the form of an array
        ''' Converts the given card, given as an array ["Value", "Color"], into a more readable format or into a format more usable by the bot. 
            It's really dirty, I know.
            If given a dirty shorthand form, it makes it pretty
            Otherwise it goes the other direction'''
        
        if ColorOnly:   #this is a short use for the function in rare cases where i got lazy during the usage of wild cards. this is meant to only be used for wild cards
            if cardArr[0] in ["r", "g", "b", "y"]:
                return ["Red", "Green", "Blue", "Yellow"][["r", "g", "b", "y"].index(cardArr[0].lower())]
            else:
                return cardArr[0].capitalize()
        finalret = [0,0] #doesnt matter what type the values are
        numtowords = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"] #to avoid retyping this 25 times
        if len(cardArr) == 1:                           #if the length is 1, then we probably need to convert it simply like this (card_Checker would catch it otherwise)
            if cardArr[0].lower() == "wild":
                return ["w"]
            elif cardArr[0].lower() == "w":
                return ["Wild"]
            if cardArr[0].lower() in ["wilddraw4", "draw4"]:
                return ["wd4"]
            else:
                return ["WildDraw4"]
        if cardArr[0].lower() == "wild":                #This if block checks for the word versions of card values
            finalret[0] = "w"
        elif cardArr[0].lower() in ["draw4", "wilddraw4"]:
            finalret[0] = "wd4"
        elif cardArr[0].lower() == "skip":
            finalret[0] = "s"
        elif cardArr[0].lower() == "draw2":
            finalret[0] = "d2"
        elif cardArr[0].lower() in ["reverse", "rev"]:
            finalret[0] = "r"
        elif cardArr[0].lower() in numtowords:
            finalret[0] = (str(numtowords.index(cardArr[0].lower())))
        if cardArr[1].lower() == "red":                 #This if block checks for the word versions of card colors
            finalret[1] = "r"
        elif cardArr[1].lower() == "blue":
            finalret[1] = "b"
        elif cardArr[1].lower() == "green":
            finalret[1] = "g"
        elif cardArr[1].lower() == "yellow":
            finalret[1] = "y"
        elif cardArr[1].lower() == "r":
            finalret[1] = "Red"
        elif cardArr[1].lower() == "b":
            finalret[1] = "Blue"
        elif cardArr[1].lower() == "y":
            finalret[1] = "Yellow"
        elif cardArr[1].lower() == "g":
            finalret[1] = "Green"
        if cardArr[0].lower() == "w":                   #This if block checks for the short versions of card values
            finalret[0] = "Wild"
        elif cardArr[0].lower() in ["wd4","d4"]:
            finalret[0] = "WildDraw4"
        elif cardArr[0].lower() == "s":
            finalret[0] = "Skip"
        elif cardArr[0].lower() == "r":
            finalret[0] = "Reverse"
        elif cardArr[0].lower() == "d2":
            finalret[0] = "Draw2"
        if cardArr[0].lower() in ["0","1","2","3","4","5","6","7","8","9"]:     #This converts a number to words in the most roundabout way I could think of
            finalret[0] = (numtowords[["0","1","2","3","4","5","6","7","8","9"].index(cardArr[0])].capitalize())
        if cardArr[0].lower() in ["wild", "draw4", "wilddraw4", "skip", "draw2", "reverse", "rev", "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"] and cardArr[1].lower() in ["r", "g", "b", "y"]:
            finalret[1] = cardArr[1]
        if cardArr[0].lower() in ["w", "d4", "wd4", "s", "d2", "r", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9"] and cardArr[1].lower() in ["red", "green", "blue", "yellow"]:
            finalret[0] = cardArr[0]
        # the last 2 ifs are used to just send the converted card forward if nothing needed to be changed
        return finalret

        
    def discard(self, card, playerID): #by this point, it is expected that the card is in string form
        ''' Send a card to the discard pile from a player's deck'''
    
        self.playerCards[playerID].remove(card)
        self.discardedCards.append(card)
        
        
    def remove_player(self, playerID):
        ''' Remove a player from the game and discard their cards. It returns a string used later on to determine what to do next'''
    
        self.discardedCards = self.discardedCards + self.playerCards[playerID]
        del self.playerCards[playerID]
        for i in range(len(self.players)):
            if self.players[i].id == playerID:
                self.players.pop(i)
                break
                
        if len(self.players) < 2:
            return "LACK OF PLAYERS"
            
        if i == self.currentTurn:
            self.next_turn()
            return "MOVETURN"
            
        if i < self.currentTurn: #this is a special case where the next time we move the turn, we might not be allowed to actually move the counter
            self.currentTurn -= 1
            return "HOLDTURN"
            
        return "PLAYERLEFT"
    
    
    def next_turn(self, peekNext = False):
        ''' Literally iterates the turn counter forward or backwards in a looping fashion'''
        if peekNext:
            fakeTurn = self.currentTurn
            if self.reverseFlag:
                fakeTurn += 1
            else:
                fakeTurn -= 1
            if fakeTurn >= len(self.players):
                fakeTurn = 0
            elif fakeTurn < 0:
                fakeTurn = len(self.players)-1
            return fakeTurn
        
        if self.reverseFlag:    #true = normal play
            self.currentTurn += 1
        else:
            self.currentTurn -= 1
        if self.currentTurn >= len(self.players):
            self.currentTurn = 0
        elif self.currentTurn < 0:
            self.currentTurn = len(self.players)-1
            
            
    async def update_Message(self):
        ''' Updates the main uno message with all necessary information'''
        
        cardCountListStr = ""
        for person in self.players:
            for k,v in self.playerCards.items():
                if k == person.id:
                    cardCountListStr = cardCountListStr + "   " + person.name + ": "+str(len(v))
        cardCountListStr = cardCountListStr.strip()
        nextPlayer = self.players[self.next_turn(peekNext=True)]
        curPlayer = self.players[self.currentTurn]
        self.colorURL = self.get_color_url(self.topCard[0].split())
        if self.topCard[0].split()[1] in ["r", "b", "g", "y"]:
            topCardStr = " ".join(self.card_Converter(self.topCard[0].split()))
        else:
            topCardStr = self.topCard[0]
        embed = discord.Embed(color = discord.Color(0xc27c0e), description="Say ^join to join.\n**Players:** "+str(len(self.players))+"\n\n**Top Card:** "+topCardStr+"\n\n**Card Count:**\n"+cardCountListStr+"\n\n**Current Turn:** "+curPlayer.name+"\n**Next Turn:** "+nextPlayer.name+"\n\n**To play a card:** ^plcard value color\n**Other Commands:** startgame, quituno, showcards, draw, pass, botjoingame")
        embed.set_author(name="Uno Game in "+self.chan.name+" started by "+self.auth.name)
        embed.set_footer(text="Produced with precision", icon_url=self.bot.user.avatar_url)
        embed.set_thumbnail(url=self.colorURL)
        self.messageHolder = await self.bot.edit_message(self.messageHolder, ".", embed=embed)
    
    
    async def clean_Messages(self, Latest=True, Alt=True):
        ''' Deletes existing queue of 2 messages from the bot if they exist'''
        
        if Latest:
            try:
                await self.bot.delete_message(self.latestMessage)
            except:
                print("Uno Latest Message was empty.")
        if Alt:
            try:
                await self.bot.delete_message(self.alternateMessage)
            except:
                print("Uno Alt Message was empty.")
    
    async def repost_Message(self):
        ''' Updates and reposts the main uno message with all necessary information'''
        
        await self.bot.delete_message(self.messageHolder)
        self.messageHolder = await self.bot.send_message(self.chan, ".")
        await self.update_Message()
    
    
    async def bot_play(self):
        ''' This runs every time it is the bot's turn and checks every possibility of something happening'''
        
        I_Can_Play = False
        if self.topCard[0].split()[1] in ["r", "b", "g", "y"]:
            topCardArr = self.topCard[0].split()
        else:
            topCardArr = self.card_Converter(self.topCard[0].split())
        for card in self.playerCards[self.bot.user.id]:
            cardArr = card.split()
            if len(cardArr) == 1 or cardArr[0] == topCardArr[0] or cardArr[1] == topCardArr[1]:
                I_Can_Play = True
                break
        if not I_Can_Play:
            #delete_later = await self.bot.send_message(self.chan, "^draw") # realism
            if len(self.gameCards) == 0 and len(self.discardedCards) == 0:
                self.next_turn()
                await self.update_Message()
                #await self.bot.delete_message(delete_later)    # realism
                await self.clean_Messages(Alt=False)
                self.latestMessage = await self.bot.send_message(self.chan, "We have run out of cards! The turn was forced forward.")
                await self.bot.send_message(self.players[self.currentTurn], "Your turn has come! Your cards:\n"+", ".join([" ".join(self.card_Converter(card.split())) for card in self.playerCards[self.players[self.currentTurn].id]]))
                return
            self.playerCards[self.bot.user.id] = self.playerCards[self.bot.user.id] + self.card_Gen(1)
            await self.update_Message()
            for card in self.playerCards[self.bot.user.id]:
                cardArr = card.split()
                if len(cardArr) == 1 or cardArr[0] == topCardArr[0] or cardArr[1] == topCardArr[1]:
                    I_Can_Play = True
                    break
            #await self.bot.delete_message(delete_later)    # realism
        if I_Can_Play:
            self.drawCounter = 0
            try:
                playedColor = cardArr[1]
            except:
                colors = ["r","b","g","y"]
                colors.pop(colors.index(topCardArr[1]))
                playedColor = colors[random.randint(0,2)]
            #delete_later2 = await self.bot.send_message(self.chan, "^plcard "+cardArr[0]+" "+playedColor)  # realism
            if cardArr[0] not in ["wd4", "w"]:
                self.discard(" ".join(cardArr), self.bot.user.id)
            else:
                self.discard(cardArr[0], self.bot.user.id)
            self.topCard = [cardArr[0]+" "+playedColor]
            if cardArr[0] == "d2":
                self.next_turn()
                self.playerCards[self.players[self.currentTurn].id].extend(self.card_Gen(2))
                poorGuy = self.players[self.currentTurn]
                self.next_turn()
                await self.clean_Messages(Alt=False)
                self.latestMessage = await self.bot.send_message(self.chan, poorGuy.name+" got skipped and drew 2 cards. It is now "+self.players[self.currentTurn].name+"'s turn.")
            elif cardArr[0] == "s":
                self.next_turn()
                poorGuy = self.players[self.currentTurn]
                self.next_turn()
                await self.clean_Messages(Alt=False)
                self.latestMessage = await self.bot.send_message(self.chan, poorGuy.name+" got skipped. It is now "+self.players[self.currentTurn].name+"'s turn.")
            elif cardArr[0] == "r":
                if self.reverseFlag:
                    self.reverseFlag = False
                else:
                    self.reverseFlag = True
                self.next_turn()
                await self.clean_Messages(Alt=False)
                self.latestMessage = await self.bot.send_message(self.chan, self.bot.user.name+" used a reverse. It is now "+self.players[self.currentTurn].name+"'s turn.")
            elif cardArr[0] == "wd4":
                self.next_turn()
                self.playerCards[self.players[self.currentTurn].id].extend(self.card_Gen(4))
                poorGuy = self.players[self.currentTurn]
                self.next_turn()
                await self.clean_Messages(Alt=False)
                self.latestMessage = await self.bot.send_message(self.chan, poorGuy.name+" got skipped and drew 4 cards. The color changed to "+self.card_Converter([playedColor], ColorOnly=True)+". It is now "+self.players[self.currentTurn].name+"'s turn.")
            elif cardArr[0] == "w":
                self.next_turn()
                await self.clean_Messages(Alt=False)
                self.latestMessage = await self.bot.send_message(self.chan, self.bot.user.name+" played a wild. The color changed to "+self.card_Converter([playedColor], ColorOnly=True)+". It is now "+self.players[self.currentTurn].name+"'s turn.")
            else:
                self.next_turn()
                await self.clean_Messages(Alt=False)
                self.latestMessage = await self.bot.send_message(self.chan, self.bot.user.name+" played a "+" ".join(self.card_Converter([cardArr[0], playedColor]))+". It is now "+self.players[self.currentTurn].name+"'s turn.")
            await self.update_Message()
            #await self.bot.delete_message(delete_later2)   # realism
            
            if self.players[self.currentTurn].id == self.bot.user.id:
                await self.bot_play()
            else:
                await self.bot.send_message(self.players[self.currentTurn], "Your turn has come! Your cards:\n"+", ".join([" ".join(self.card_Converter(card.split())) for card in self.playerCards[self.players[self.currentTurn].id]]))
            try:
                if len(self.playerCards[self.bot.user.id]) == 1:
                    delete_uno = await self.bot.send_message(self.chan, "UNO! "+self.bot.user.name+" has 1 card left.")
                    await self.bot.delete_message_later(delete_uno, 30)
                elif len(self.playerCards[self.bot.user.id]) == 0:
                    del self.bot.UnoGames[self.chan.id]
                    return await self.bot.send_message(self.chan, "The game is over. "+self.bot.user.name+" has won.")
            except:
                print("The game has ended and for some reason things broke. Notification still probably went out.")
        else:
            #delete_later = await self.bot.send_message(self.chan, "^pass") # realism
            self.drawCounter = 0
            self.next_turn()
            await self.clean_Messages(Alt=False)
            self.latestMessage = await self.bot.send_message(self.chan, "Pass! It is now "+self.players[self.currentTurn].name+"'s turn.")
            await self.bot.send_message(self.players[self.currentTurn], "Your turn has come! Your cards:\n"+", ".join([" ".join(self.card_Converter(card.split())) for card in self.playerCards[self.players[self.currentTurn].id]]))
            #await self.bot.delete_message(delete_later)    # realism
        
        
        
        
        
        
        
        
        
        
        
        
        
        

        
