import os
import re
import gc
import sys
import time
import shlex
import shutil
import inspect
import aiohttp
import discord
import asyncio
import random
import requests
import traceback
import subprocess
import youtube_dl
from bs4 import BeautifulSoup as bS
from threading import Timer
import urllib.request
from pprint import pprint
import difflib

from discord import utils
from discord.object import Object
from discord.enums import ChannelType
from discord.enums import MessageType
from discord.enums import Status
from discord.voice_client import VoiceClient
from discord.ext.commands.bot import _get_variable

from io import BytesIO
from functools import wraps
from textwrap import dedent
from datetime import timedelta
from datetime import datetime
from random import choice, shuffle
from collections import defaultdict

from musicbot.playlist import Playlist
from musicbot.player import MusicPlayer
from musicbot.player import MusicPlayerState
from musicbot.config import Config, ConfigDefaults
from musicbot.permissions import Permissions, PermissionsDefaults
from musicbot.utils import load_file, write_file, sane_round_int

from . import exceptions
from . import downloader
from .opus_loader import load_opus_lib
from .constants import VERSION as BOTVERSION
from .constants import DISCORD_MSG_CHAR_LIMIT, AUDIO_CACHE_PATH


load_opus_lib()
freqdict = dict()
freqlist = list()
f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/wordfreq.txt", "r")
for line in f:
    freqdict[re.search("(.+),", line).group(1)] = re.search(".+,(\d+)", line).group(1)
f.close()
for k,v in freqdict.items():
    for _ in range(int(v)):
        freqlist.append(k)
punctmrks = [",",".",":","-","!","(",")","?","'",";","\""]
unotable = [["."],[".",0,0,0,0,0],[0],[0],[0],[0],".",[0]]
barquiet = 0
expired_cdt = 0
expired_martyr = 0
nxtmsgQ = []
lockedvolume = 0
baruse = 1
barsaver = 0
ttstimer = 0
nxtttsQ = []
nxtttsQuse = 0




def cards(x):           #given x, this returns x number of cards as an array
    cardlist = ["1 b", "2 b", "3 b", "4 b", "5 b", "6 b", "7 b", "8 b", "9 b", "0 b", "1 y", "2 y", "3 y", "4 y", "5 y", "6 y", "7 y", "8 y", "9 y", "0 y", "1 g", "2 g", "3 g", "4 g", "5 g", "6 g", "7 g", "8 g", "9 g", "0 g", "1 r", "2 r", "3 r", "4 r", "5 r", "6 r", "7 r", "8 r", "9 r", "0 r", "wd4", "wd4", "wd4", "wd4", "d2 r", "d2 r", "d2 y", "d2 y", "d2 g", "d2 g", "d2 b", "d2 b", "s r", "s r", "s g", "s g", "s b", "s b", "s y", "s y", "r r", "r r", "r y", "r y", "r b", "r b", "r g", "r g", "w", "w", "w", "w"]
    givencards = []
    for _ in range(x):
        givencards.append(cardlist[random.randint(0,71)])
    return givencards
def iscard(cardArr):    #this expects an array param given from message_content.split()
    if cardArr[0].lower() in ["w", "wd4", "s", "r", "d2", "wild", "wilddraw4", "draw4", "skip", "reverse", "draw2"]:  #w and wd4 technically have no color but need color params
        if cardArr[1].lower() in ["r", "g", "b", "y", "red", "green", "blue", "yellow"]:
            return True
    if cardArr[0].lower() in ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]:
        if cardArr[1].lower() in ["r", "g", "b", "y", "red", "green", "blue", "yellow"]:
            return True
    return False
def nextturn(): #pushes nextturn where we use optional(channelname) as a var if the table for it doesnt exist
    global unotable
    #print("from turn", unotable[2][0])
    #print(unotable[1][0])
    if unotable[1][0] == True:    #if Reverse is True, turn + 1
        unotable[2][0] = unotable[2][0] + 1
    else:
        unotable[2][0] = unotable[2][0] - 1
    if unotable[2][0] > unotable[3][0]:
        unotable[2][0] = 0          #to avoid turns running out of bound (turns attach to players)
    if unotable[2][0] < 0:
        unotable[2][0] = unotable[3][0]
    #print("to turn", unotable[2][0])
    #print(unotable[1][0])
    
    
    
def convcard(card): #card is an array        #returns either a clean format of the card if given "2 b" or a dirty format for "2 blue"
    finalret = [0,0]
    numtowords = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]
    if len(card) == 1:
        if card[0].lower() == "wild":
            return ["w"]
        elif card[0].lower() == "w":
            return ["Wild"]
        if card[0].lower() in ["wilddraw4", "draw4"]:
            return ["wd4"]
        else:
            return ["WildDraw4"]
    if card[0].lower() == "wild":
        finalret[0] = "w"
    elif card[0].lower() in ["draw4", "wilddraw4"]:
        finalret[0] = "wd4"
    elif card[0].lower() == "skip":
        finalret[0] = "s"
    elif card[0].lower() == "draw2":
        finalret[0] = "d2"
    elif card[0].lower() in ["reverse", "rev"]:
        finalret[0] = "r"
    elif card[0].lower() in numtowords:
        finalret[0] = (str(numtowords.index(card[0].lower())))
    if card[1].lower() == "red":
        finalret[1] = "r"
    elif card[1].lower() == "blue":
        finalret[1] = "b"
    elif card[1].lower() == "green":
        finalret[1] = "g"
    elif card[1].lower() == "yellow":
        finalret[1] = "y"
    elif card[1].lower() == "r":
        finalret[1] = "Red"
    elif card[1].lower() == "b":
        finalret[1] = "Blue"
    elif card[1].lower() == "y":
        finalret[1] = "Yellow"
    elif card[1].lower() == "g":
        finalret[1] = "Green"
    if card[0].lower() == "w":
        finalret[0] = "Wild"
    elif card[0].lower() in ["wd4","d4"]:
        finalret[0] = "WildDraw4"
    elif card[0].lower() == "s":
        finalret[0] = "Skip"
    elif card[0].lower() == "r":
        finalret[0] = "Reverse"
    elif card[0].lower() == "d2":
        finalret[0] = "Draw2"
    if card[0].lower() in ["0","1","2","3","4","5","6","7","8","9"]:
        finalret[0] = (numtowords[["0","1","2","3","4","5","6","7","8","9"].index(card[0])].capitalize())
    if card[0].lower() in ["wild", "draw4", "wilddraw4", "skip", "draw2", "reverse", "rev", "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"] and card[1].lower() in ["r", "g", "b", "y"]:
        #print("AMBIGUITY CAUGHT!")
        finalret[1] = card[1]
    if card[0].lower() in ["w", "d4", "wd4", "s", "d2", "r", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9"] and card[1].lower() in ["red", "green", "blue", "yellow"]:
        #print("AMBIGUITY CAUGHT!")
        finalret[0] = card[0]
    #print("converted ", card)
    #print("to ", finalret)
    return finalret
def colorize(card, server):        #takes an array of a card and returns a new array
    global unotable
    retlist = [card[0], 0]
    if len(card) == 1:
        return card
    if card[1].lower() in ["g", "green"]:
        if server.name == "Ghost Division":
            retlist[1] = "<:unoGREEN:245719805896818699>"
        if server.name == "CBU BEST":
            retlist[1] = "<:unoGREEN:287822013916119040>"
    elif card[1].lower() in ["r", "red"]:
        if server.name == "Ghost Division":
            retlist[1] = "<:unoRED:245719814251872256>"
        if server.name == "CBU BEST":
            retlist[1] = "<:unoRED:287822006496395264>"
    elif card[1].lower() in ["y", "yellow"]:
        if server.name == "Ghost Division":
            retlist[1] = "<:unoYELLOW:245719822573371393>"
        if server.name == "CBU BEST":
            retlist[1] = "<:unoYELLOW:287821996362825769>"
    elif card[1].lower() in ["b", "blue"]:
        if server.name == "Ghost Division":
            retlist[1] = "<:unoBLUE:245719795960512512>"
        if server.name == "CBU BEST":
            retlist[1] = "<:unoBLUE:287822021037916161>"
    return retlist
def hascard(card, plyr):        #plyr must be a string; checks if str:card is in the array value attached to key plyr in the players dictionary
    global unotable
    if card in unotable[4][plyr]:        #[4][0] is a dictionary, [4][0][plyr] is an array/list
        return True
    return False
def delcard(card, plyr):      #card and plyr are strings
    global unotable
    unotable[4][plyr].remove(card)
def remplayer(plyr):    #plyr must be a string
    global unotable
    #unotable[4].pop(plyr)
    del unotable[4][plyr]
    if (unotable[3][0]-1) < 1:
        #await discord.Client.send_message(unotable[0][1], "The game must end because there are too few players left.")
        unotable[5].remove(plyr)
        unotable = [["."],[".",0,0,0,0,0,0],[],[],[],[],".",[]]
        return "LACK OF PLAYERS"
    if unotable[2][0] == unotable[5].index(plyr):
        nextturn()
        unotable[5].remove(plyr)
        #  await discord.Client.send_message(unotable[0][1], "It is now "+nnick+"'s turn.")
        # await discord.Client.send_message(unotable[0][1], "The top card is: "+unotable[6])
        unotable[3][0] = unotable[3][0] - 1
        return "MOVETURN"
    for i in range(len(unotable[7])):
        if unotable[7][i].name == plyr:
            unotable[7].pop(i)
            unotable[5].remove(plyr)
            unotable[3][0] = unotable[3][0] - 1
            return "PLAYERLEFT"

class SkipState:
    def __init__(self):
        self.skippers = set()
        self.skip_msgs = set()

    @property
    def skip_count(self):
        return len(self.skippers)

    def reset(self):
        self.skippers.clear()
        self.skip_msgs.clear()

    def add_skipper(self, skipper, msg):
        self.skippers.add(skipper)
        self.skip_msgs.add(msg)
        return self.skip_count


class Response:
    def __init__(self, content, reply=False, delete_after=0):
        self.content = content
        self.reply = reply
        self.delete_after = delete_after





class MusicBot(discord.Client):
#    def resettimer(self, channel):
#        global timerun
#        global chtime
#        global timenow
#        global timethen
#        global tinsecs
#        timenow = datetime.today()
#        timethen = timenow.replace(day=timenow.day, hour=timenow.hour, minute=timenow.minute, second=timenow.second+5, microsecond=0)
#        chtime = timethen-timenow
#        tinsecs = chtime.seconds+1
#        args = [channel]
#        print(channel)
#        timerun = Timer(5, self._timernoon, args=args)
#        loop = asyncio.get_event_loop()
#        tasks = [asyncio.ensure_future(self._timernoon(channel))]
#        self.loop.run_until_complete(asyncio.gather(self._timernoon))
#        loop.close()
#        timerun.start()
#    async def _timernoon(self, channel):
#        await self.send_message(channel, "Test successful.")
#        self.resettimer(channel)
    def __init__(self, config_file=ConfigDefaults.options_file, perms_file=PermissionsDefaults.perms_file):
        self.players = {}
        self.the_voice_clients = {}
        self.locks = defaultdict(asyncio.Lock)
        self.voice_client_connect_lock = asyncio.Lock()
        self.voice_client_move_lock = asyncio.Lock()

        self.config = Config(config_file)
        self.permissions = Permissions(perms_file, grant_all=[self.config.owner_id])

        self.blacklist = set(load_file(self.config.blacklist_file))
        self.autoplaylist = load_file(self.config.auto_playlist_file)
        self.downloader = downloader.Downloader(download_folder='audio_cache')

        self.exit_signal = None
        self.init_ok = False
        self.cached_client_id = None
        self.cap_msg_in_a_row = 0
        self.cap_msg_nick = ""
        
        fl = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/idlist.txt", "r")
        self.newmemberlist = []
        for line in fl:
            self.newmemberlist.append(line.strip())
        fl.close()
        
        fr = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/reminders.txt", "r")
        self.reminderlist = []
        for line in fr:
            self.reminderlist.append(line.strip().split("@!@"))
        fr.close()
        self.listToBurn = []
        self.reminderlist.pop(0)
        
        self.activityDict = dict()
        fa = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/activity.txt", "r")
        for line in fa:
            self.activityDict[line.split("@")[0]] = [line.split("@")[1], line.split("@")[2]]
        fa.close()
        
        
        self.mblock = False
        self.mblockchanlist = []
        self.linkblock = False
        self.linkblockchanlist = []
        
        self.invitelists = {}
        self.polls = []
        self.modchan = None
        
        self.stop_GTQ = False
        
        

        if not self.autoplaylist:
            print("Warning: Autoplaylist is empty, disabling.")
            self.config.auto_playlist = False

        # TODO: Do these properly
        ssd_defaults = {'last_np_msg': None, 'auto_paused': False}
        self.server_specific_data = defaultdict(lambda: dict(ssd_defaults))

        super().__init__()
        self.aiosession = aiohttp.ClientSession(loop=self.loop)
        self.http.user_agent += ' MusicBot/%s' % BOTVERSION

    # TODO: Add some sort of `denied` argument for a message to send when someone else tries to use it
    def owner_only(func):
        @wraps(func)
        async def wrapper(self, *args, **kwargs):
            # Only allow the owner to use these commands
            orig_msg = _get_variable('message')

            if not orig_msg or orig_msg.author.id == self.config.owner_id:
                return await func(self, *args, **kwargs)
            else:
                raise exceptions.PermissionsError("only the owner can use this command", expire_in=30)

        return wrapper

    @staticmethod
    def _fixg(x, dp=2):
        return ('{:.%sf}' % dp).format(x).rstrip('0').rstrip('.')

    def _get_owner(self, voice=False):
        if voice:
            for server in self.servers:
                for channel in server.channels:
                    for m in channel.voice_members:
                        if m.id == self.config.owner_id:
                            return m
        else:
            return discord.utils.find(lambda m: m.id == self.config.owner_id, self.get_all_members())










    def _delete_old_audiocache(self, path=AUDIO_CACHE_PATH):
        try:
            shutil.rmtree(path)
            return True
        except:
            try:
                os.rename(path, path + '__')
            except:
                return False
            try:
                shutil.rmtree(path)
            except:
                os.rename(path + '__', path)
                return False

        return True

    # TODO: autosummon option to a specific channel
    async def _auto_summon(self):
        owner = self._get_owner(voice=True)
        if owner:
            self.safe_print("Found owner in \"%s\", attempting to join..." % owner.voice_channel.name)
            # TODO: Effort
            await self.cmd_summon(owner.voice_channel, owner, None)
            return owner.voice_channel



    async def _autojoin_channels(self, channels):
        joined_servers = []

        for channel in channels:
            if channel.server in joined_servers:
                print("Already joined a channel in %s, skipping" % channel.server.name)
                continue

            if channel and channel.type == discord.ChannelType.voice:
                self.safe_print("Attempting to autojoin %s in %s" % (channel.name, channel.server.name))

                chperms = channel.permissions_for(channel.server.me)

                if not chperms.connect:
                    self.safe_print("Cannot join channel \"%s\", no permission." % channel.name)
                    continue

                elif not chperms.speak:
                    self.safe_print("Will not join channel \"%s\", no permission to speak." % channel.name)
                    continue

                try:
                    player = await self.get_player(channel, create=True)

                    if player.is_stopped:
                        player.play()

                    if self.config.auto_playlist:
                        await self.on_player_finished_playing(player)

                    joined_servers.append(channel.server)
                except Exception as e:
                    if self.config.debug_mode:
                        traceback.print_exc()
                    print("Failed to join", channel.name)

            elif channel:
                print("Not joining %s on %s, that's a text channel." % (channel.name, channel.server.name))

            else:
                print("Invalid channel thing: " + channel)

    async def _wait_delete_msg(self, message, after):
        await asyncio.sleep(after)
        await self.safe_delete_message(message)

    # TODO: Check to see if I can just move this to on_message after the response check
    async def _manual_delete_check(self, message, *, quiet=False):
        if self.config.delete_invoking:
            await self.safe_delete_message(message, quiet=quiet)

    async def _check_ignore_non_voice(self, msg):
        vc = msg.server.me.voice_channel

        # If we've connected to a voice chat and we're in the same voice channel
        if not vc or vc == msg.author.voice_channel:
            return True
        else:
            raise exceptions.PermissionsError(
                "you cannot use this command when not in the voice channel (%s)" % vc.name, expire_in=30)

    async def generate_invite_link(self, *, permissions=None, server=None):
        if not self.cached_client_id:
            appinfo = await self.application_info()
            self.cached_client_id = appinfo.id

        return discord.utils.oauth_url(self.cached_client_id, permissions=permissions, server=server)

    async def get_voice_client(self, channel):
        if isinstance(channel, Object):
            channel = self.get_channel(channel.id)

        if getattr(channel, 'type', ChannelType.text) != ChannelType.voice:
            raise AttributeError('Channel passed must be a voice channel')

        with await self.voice_client_connect_lock:
            server = channel.server
            if server.id in self.the_voice_clients:
                return self.the_voice_clients[server.id]

            s_id = self.ws.wait_for('VOICE_STATE_UPDATE', lambda d: d.get('user_id') == self.user.id)
            _voice_data = self.ws.wait_for('VOICE_SERVER_UPDATE', lambda d: True)

            await self.ws.voice_state(server.id, channel.id)

            s_id_data = await asyncio.wait_for(s_id, timeout=10, loop=self.loop)
            voice_data = await asyncio.wait_for(_voice_data, timeout=10, loop=self.loop)
            session_id = s_id_data.get('session_id')

            kwargs = {
                'user': self.user,
                'channel': channel,
                'data': voice_data,
                'loop': self.loop,
                'session_id': session_id,
                'main_ws': self.ws
            }
            voice_client = VoiceClient(**kwargs)
            self.the_voice_clients[server.id] = voice_client

            retries = 3
            for x in range(retries):
                try:
                    print("Attempting connection...")
                    await asyncio.wait_for(voice_client.connect(), timeout=10, loop=self.loop)
                    print("Connection established.")
                    break
                except:
                    traceback.print_exc()
                    print("Failed to connect, retrying (%s/%s)..." % (x+1, retries))
                    await asyncio.sleep(1)
                    await self.ws.voice_state(server.id, None, self_mute=True)
                    await asyncio.sleep(1)

                    if x == retries-1:
                        raise exceptions.HelpfulError(
                            "Cannot establish connection to voice chat.  "
                            "Something may be blocking outgoing UDP connections.",

                            "This may be an issue with a firewall blocking UDP.  "
                            "Figure out what is blocking UDP and disable it.  "
                            "It's most likely a system firewall or overbearing anti-virus firewall.  "
                        )

            return voice_client

    async def mute_voice_client(self, channel, mute):
        await self._update_voice_state(channel, mute=mute)

    async def deafen_voice_client(self, channel, deaf):
        await self._update_voice_state(channel, deaf=deaf)

    async def move_voice_client(self, channel):
        await self._update_voice_state(channel)

    async def reconnect_voice_client(self, server):
        if server.id not in self.the_voice_clients:
            return

        vc = self.the_voice_clients.pop(server.id)
        _paused = False

        player = None
        if server.id in self.players:
            player = self.players[server.id]
            if player.is_playing:
                player.pause()
                _paused = True

        try:
            await vc.disconnect()
        except:
            print("Error disconnecting during reconnect")
            traceback.print_exc()

        await asyncio.sleep(0.1)

        if player:
            new_vc = await self.get_voice_client(vc.channel)
            player.reload_voice(new_vc)

            if player.is_paused and _paused:
                player.resume()

    async def disconnect_voice_client(self, server):
        if server.id not in self.the_voice_clients:
            return

        if server.id in self.players:
            self.players.pop(server.id).kill()

        await self.the_voice_clients.pop(server.id).disconnect()

    async def disconnect_all_voice_clients(self):
        for vc in self.the_voice_clients.copy().values():
            await self.disconnect_voice_client(vc.channel.server)

    async def _update_voice_state(self, channel, *, mute=False, deaf=False):
        if isinstance(channel, Object):
            channel = self.get_channel(channel.id)

        if getattr(channel, 'type', ChannelType.text) != ChannelType.voice:
            raise AttributeError('Channel passed must be a voice channel')

        # I'm not sure if this lock is actually needed
        with await self.voice_client_move_lock:
            server = channel.server

            payload = {
                'op': 4,
                'd': {
                    'guild_id': server.id,
                    'channel_id': channel.id,
                    'self_mute': mute,
                    'self_deaf': deaf
                }
            }

            await self.ws.send(utils.to_json(payload))
            self.the_voice_clients[server.id].channel = channel

    async def get_player(self, channel, create=False) -> MusicPlayer:
        server = channel.server

        if server.id not in self.players:
            if not create:
                raise exceptions.CommandError(
                    'The bot is not in a voice channel.  '
                    'Use %ssummon to summon it to your voice channel.' % self.config.command_prefix)

            voice_client = await self.get_voice_client(channel)

            playlist = Playlist(self)
            player = MusicPlayer(self, voice_client, playlist) \
                .on('play', self.on_player_play) \
                .on('resume', self.on_player_resume) \
                .on('pause', self.on_player_pause) \
                .on('stop', self.on_player_stop) \
                .on('finished-playing', self.on_player_finished_playing) \
                .on('entry-added', self.on_player_entry_added)

            player.skip_state = SkipState()
            self.players[server.id] = player

        return self.players[server.id]

    async def on_player_play(self, player, entry):
        await self.update_now_playing(entry)
        player.skip_state.reset()
        try:
            channel = entry.meta.get('channel', None)
            author = entry.meta.get('author', None)
        except:
            return ""
        if channel and author:
            last_np_msg = self.server_specific_data[channel.server]['last_np_msg']
            if last_np_msg and last_np_msg.channel == channel:

                async for lmsg in self.logs_from(channel, limit=1):
                    if lmsg != last_np_msg and last_np_msg:
                        await self.safe_delete_message(last_np_msg)
                        self.server_specific_data[channel.server]['last_np_msg'] = None
                    break  # This is probably redundant

            if self.config.now_playing_mentions:
                newmsg = '%s - your song **%s** is now playing in %s!' % (
                    entry.meta['author'].mention, entry.title, player.voice_client.channel.name)
            else:
                newmsg = 'Now playing in %s: **%s**' % (
                    player.voice_client.channel.name, entry.title)

            if self.server_specific_data[channel.server]['last_np_msg']:
                self.server_specific_data[channel.server]['last_np_msg'] = await self.safe_edit_message(last_np_msg, newmsg, send_if_fail=True)
            else:
                self.server_specific_data[channel.server]['last_np_msg'] = await self.safe_send_message(channel, newmsg)

    async def on_player_resume(self, entry, **_):
        await self.update_now_playing(entry)

    async def on_player_pause(self, entry, **_):
        await self.update_now_playing(entry, True)

    async def on_player_stop(self, **_):
        await self.update_now_playing()

    async def on_player_finished_playing(self, player, **_):
        if not player.playlist.entries and not player.current_entry and self.config.auto_playlist:
            while self.autoplaylist:
                song_url = choice(self.autoplaylist)
                info = await self.downloader.safe_extract_info(player.playlist.loop, song_url, download=False, process=False)

                if not info:
                    self.autoplaylist.remove(song_url)
                    self.safe_print("[Info] Removing unplayable song from autoplaylist: %s" % song_url)
                    write_file(self.config.auto_playlist_file, self.autoplaylist)
                    continue

                if info.get('entries', None):  # or .get('_type', '') == 'playlist'
                    pass  # Wooo playlist
                    # Blarg how do I want to do this

                # TODO: better checks here
                try:
                    await player.playlist.add_entry(song_url, channel=None, author=None)
                except exceptions.ExtractionError as e:
                    print("Error adding song from autoplaylist:", e)
                    continue

                break

            if not self.autoplaylist:
                print("[Warning] No playable songs in the autoplaylist, disabling.")
                self.config.auto_playlist = False

    async def on_player_entry_added(self, playlist, entry, **_):
        pass

    async def update_now_playing(self, entry=None, is_paused=False):
        game = None

        if self.user.bot:
            activeplayers = sum(1 for p in self.players.values() if p.is_playing)
            if activeplayers > 1:
                game = discord.Game(name="music on %s servers" % activeplayers)
                entry = None

            elif activeplayers == 1:
                player = discord.utils.get(self.players.values(), is_playing=True)
                entry = player.current_entry

        if entry:
            prefix = u'\u275A\u275A ' if is_paused else ''

            name = u'{}{}'.format(prefix, entry.title)[:128]
            game = discord.Game(name=name)
        if type(entry) == str:
            return ""
        await self.change_presence(game=game)


    async def safe_send_message(self, dest, content, *, tts=False, expire_in=0, also_delete=None, quiet=False):
        msg = None
        try:
            msg = await self.send_message(dest, content, tts=tts)

            if msg and expire_in:
                asyncio.ensure_future(self._wait_delete_msg(msg, expire_in))

            if also_delete and isinstance(also_delete, discord.Message):
                asyncio.ensure_future(self._wait_delete_msg(also_delete, expire_in))

        except discord.Forbidden:
            if not quiet:
                self.safe_print("Warning: Cannot send message to %s, no permission" % dest.name)

        except discord.NotFound:
            if not quiet:
                self.safe_print("Warning: Cannot send message to %s, invalid channel?" % dest.name)

        return msg

    async def safe_delete_message(self, message, *, quiet=False):
        try:
            return await self.delete_message(message)

        except discord.Forbidden:
            if not quiet:
                self.safe_print("Warning: Cannot delete message \"%s\", no permission" % message.clean_content)

        except discord.NotFound:
            if not quiet:
                self.safe_print("Warning: Cannot delete message \"%s\", message not found" % message.clean_content)

    async def safe_edit_message(self, message, new, *, send_if_fail=False, quiet=False):
        try:
            return await self.edit_message(message, new)

        except discord.NotFound:
            if not quiet:
                self.safe_print("Warning: Cannot edit message \"%s\", message not found" % message.clean_content)
            if send_if_fail:
                if not quiet:
                    print("Sending instead")
                return await self.safe_send_message(message.channel, new)

    def safe_print(self, content, *, end='\n', flush=True):
        sys.stdout.buffer.write((content + end).encode('utf-8', 'replace'))
        if flush: sys.stdout.flush()

    async def send_typing(self, destination):
        try:
            return await super().send_typing(destination)
        except discord.Forbidden:
            if self.config.debug_mode:
                print("Could not send typing to %s, no permssion" % destination)

    async def edit_profile(self, **fields):
        if self.user.bot:
            return await super().edit_profile(**fields)
        else:
            return await super().edit_profile(self.config._password,**fields)

    def _cleanup(self):
        try:
            self.loop.run_until_complete(self.logout())
        except: # Can be ignored
            pass

        pending = asyncio.Task.all_tasks()
        gathered = asyncio.gather(*pending)

        try:
            gathered.cancel()
            self.loop.run_until_complete(gathered)
            gathered.exception()
        except: # Can be ignored
            pass

    # noinspection PyMethodOverriding
    def run(self):
        try:
            self.loop.run_until_complete(self.start(*self.config.auth))

        except discord.errors.LoginFailure:
            # Add if token, else
            raise exceptions.HelpfulError(
                "Bot cannot login, bad credentials.",
                "Fix your Email or Password or Token in the options file.  "
                "Remember that each field should be on their own line.")

        finally:
            try:
                self._cleanup()
            except Exception as e:
                print("Error in cleanup:", e)

            self.loop.close()
            if self.exit_signal:
                raise self.exit_signal

    async def logout(self):
        await self.disconnect_all_voice_clients()
        return await super().logout()

    async def on_error(self, event, *args, **kwargs):
        ex_type, ex, stack = sys.exc_info()

        if ex_type == exceptions.HelpfulError:
            print("Exception in", event)
            print(ex.message)

            await asyncio.sleep(2)  # don't ask
            await self.logout()

        elif issubclass(ex_type, exceptions.Signal):
            self.exit_signal = ex_type
            await self.logout()

        else:
            traceback.print_exc()

    async def on_resumed(self):
        for vc in self.the_voice_clients.values():
            vc.main_ws = self.ws

    async def on_ready(self):
        print('\rConnected!  Musicbot v%s\n' % BOTVERSION)
        print(list(self.servers))
        for x in self.servers:
            print(x)
            print(x.name)
            if x.name == "Ghost Division":
                server = x
        #self.resettimer(server.default_channel)
        if self.config.owner_id == self.user.id:
            raise exceptions.HelpfulError(
                "Your OwnerID is incorrect or you've used the wrong credentials.",

                "The bot needs its own account to function.  "
                "The OwnerID is the id of the owner, not the bot.  "
                "Figure out which one is which and use the correct information.")

        self.init_ok = True

        self.safe_print("Bot:   %s/%s#%s" % (self.user.id, self.user.name, self.user.discriminator))

        owner = self._get_owner(voice=True) or self._get_owner()
        if owner and self.servers:
            self.safe_print("Owner: %s/%s#%s\n" % (owner.id, owner.name, owner.discriminator))

            print('Server List:')
            [self.safe_print(' - ' + s.name) for s in self.servers]

        elif self.servers:
            print("Owner could not be found on any server (id: %s)\n" % self.config.owner_id)

            print('Server List:')
            [self.safe_print(' - ' + s.name) for s in self.servers]

        else:
            print("Owner unknown, bot is not on any servers.")
            if self.user.bot:
                print("\nTo make the bot join a server, paste this link in your browser.")
                print("Note: You should be logged into your main account and have \n"
                      "manage server permissions on the server you want the bot to join.\n")
                print("    " + await self.generate_invite_link())

        print()

        if self.config.bound_channels:
            chlist = set(self.get_channel(i) for i in self.config.bound_channels if i)
            chlist.discard(None)
            invalids = set()

            invalids.update(c for c in chlist if c.type == discord.ChannelType.voice)
            chlist.difference_update(invalids)
            self.config.bound_channels.difference_update(invalids)

            print("Bound to text channels:")
            [self.safe_print(' - %s/%s' % (ch.server.name.strip(), ch.name.strip())) for ch in chlist if ch]

            if invalids and self.config.debug_mode:
                print("\nNot binding to voice channels:")
                [self.safe_print(' - %s/%s' % (ch.server.name.strip(), ch.name.strip())) for ch in invalids if ch]

            print()

        else:
            print("Not bound to any text channels")

        if self.config.autojoin_channels:
            chlist = set(self.get_channel(i) for i in self.config.autojoin_channels if i)
            chlist.discard(None)
            invalids = set()

            invalids.update(c for c in chlist if c.type == discord.ChannelType.text)
            chlist.difference_update(invalids)
            self.config.autojoin_channels.difference_update(invalids)

            print("Autojoining voice chanels:")
            [self.safe_print(' - %s/%s' % (ch.server.name.strip(), ch.name.strip())) for ch in chlist if ch]

            if invalids and self.config.debug_mode:
                print("\nCannot join text channels:")
                [self.safe_print(' - %s/%s' % (ch.server.name.strip(), ch.name.strip())) for ch in invalids if ch]

            autojoin_channels = chlist

        else:
            print("Not autojoining any voice channels")
            autojoin_channels = set()

        print()
        print("Options:")

        self.safe_print("  Command prefix: " + self.config.command_prefix)
        print("  Default volume: %s%%" % int(self.config.default_volume * 100))
        print("  Skip threshold: %s votes or %s%%" % (
            self.config.skips_required, self._fixg(self.config.skip_ratio_required * 100)))
        print("  Now Playing @mentions: " + ['Disabled', 'Enabled'][self.config.now_playing_mentions])
        print("  Auto-Summon: " + ['Disabled', 'Enabled'][self.config.auto_summon])
        print("  Auto-Playlist: " + ['Disabled', 'Enabled'][self.config.auto_playlist])
        print("  Auto-Pause: " + ['Disabled', 'Enabled'][self.config.auto_pause])
        print("  Delete Messages: " + ['Disabled', 'Enabled'][self.config.delete_messages])
        if self.config.delete_messages:
            print("    Delete Invoking: " + ['Disabled', 'Enabled'][self.config.delete_invoking])
        print("  Debug Mode: " + ['Disabled', 'Enabled'][self.config.debug_mode])
        print("  Downloaded songs will be %s" % ['deleted', 'saved'][self.config.save_videos])
        print()

        # maybe option to leave the ownerid blank and generate a random command for the owner to use
        # wait_for_message is pretty neato

        if not self.config.save_videos and os.path.isdir(AUDIO_CACHE_PATH):
            if self._delete_old_audiocache():
                print("Deleting old audio cache")
            else:
                print("Could not delete old audio cache, moving on.")

        if self.config.autojoin_channels:
            await self._autojoin_channels(autojoin_channels)

        elif self.config.auto_summon:
            print("Attempting to autosummon...", flush=True)

            # waitfor + get value
            owner_vc = await self._auto_summon()

            if owner_vc:
                print("Done!", flush=True)  # TODO: Change this to "Joined server/channel"
                if self.config.auto_playlist:
                    print("Starting auto-playlist")
                    await self.on_player_finished_playing(await self.get_player(owner_vc))
            else:
                print("Owner not found in a voice channel, could not autosummon.")

        print()
        for x in self.servers:
            if x.name == "Ghost Division":
                srvr = x
                self.gdsrvr = x
        for x in srvr.channels:
                if x.id == "264837364415725568":
                    self.modchan = x
                if x.id == "249261582532476929":
                    self.testchan = x
                if x.id == "306180221781016576":
                    self.alertchan = x
        for x in self.servers:
            self.invitelists[x.name] = await self.invites_from(x)
        for role in srvr.roles:
            if role.name == "Admin":
                self.adminrole = role
        #await self.send_message(srvr, "BarinadeBot is online.")
        self.loop.call_later(1, self._wordofthedayloop, self.loop.time(), srvr)
        self.loop.call_later(1, self._checkinvitelistloop, srvr)
        self.loop.call_later(1, self._remind_checker)
        # t-t-th-th-that's all folks!

    async def cmd_help(self, permissions, author, command=None):
        """
        Usage:
            !help [command]

        Prints a help message.
        If a command is specified, it prints a help message for that command.
        Otherwise, it lists the available commands.
        """

        if command:
            cmd = getattr(self, 'cmd_' + command, None)
            if cmd:
                return Response(
                    "```\n{}```".format(
                        dedent(cmd.__doc__),
                        command_prefix=self.config.command_prefix
                    ),
                    delete_after=60
                )
            else:
                return Response("No such command", delete_after=10)

        else:
            helpmsg = "**Commands available for your group, "+self.permissions.for_user(author).name+" (say !help command for help with those commands)**\n```"
            commands = []

            for att in dir(self):
                if att.startswith('cmd_') and att != 'cmd_help':
                    command_name = att.replace('cmd_', '').lower()
                    if self.permissions.for_user(author).command_whitelist and command_name not in self.permissions.for_user(author).command_whitelist:
                        print("Command not whitelisted")
                    elif self.permissions.for_user(author).command_blacklist and command_name in self.permissions.for_user(author).command_blacklist:
                        print("Command blacklisted")
                    else:
                        commands.append("{}{}".format(self.config.command_prefix, command_name))

            helpmsg += ", ".join(commands)
            helpmsg += "```"
    #        helpmsg += "https://github.com/SexualRhinoceros/MusicBot/wiki/Commands-list"

            return Response(helpmsg, reply=True, delete_after=60)

    async def cmd_blacklist(self, message, user_mentions, option, something):
        """
        Usage:
            !blacklist [ + | - | add | remove ] @UserName [@UserName2 ...]

        Add or remove users to the blacklist.
        Blacklisted users are forbidden from using bot commands.
        """

        if not user_mentions:
            raise exceptions.CommandError("No users listed.", expire_in=20)

        if option not in ['+', '-', 'add', 'remove']:
            raise exceptions.CommandError(
                'Invalid option "%s" specified, use +, -, add, or remove' % option, expire_in=20
            )

        for user in user_mentions.copy():
            if user.id == self.config.owner_id:
                print("[Commands:Blacklist] The owner cannot be blacklisted.")
                user_mentions.remove(user)

        old_len = len(self.blacklist)

        if option in ['+', 'add']:
            self.blacklist.update(user.id for user in user_mentions)

            write_file(self.config.blacklist_file, self.blacklist)

            return Response(
                '%s users have been added to the blacklist' % (len(self.blacklist) - old_len),
                reply=True, delete_after=10
            )

        else:
            if self.blacklist.isdisjoint(user.id for user in user_mentions):
                return Response('none of those users are in the blacklist.', reply=True, delete_after=10)

            else:
                self.blacklist.difference_update(user.id for user in user_mentions)
                write_file(self.config.blacklist_file, self.blacklist)

                return Response(
                    '%s users have been removed from the blacklist' % (old_len - len(self.blacklist)),
                    reply=True, delete_after=10
                )

    async def cmd_id(self, author, user_mentions):
        """
        Usage:
            !id [@user]

        Tells the user their id or the id of another user.
        """
        if not user_mentions:
            return Response('your id is `%s`' % author.id, reply=True, delete_after=35)
        else:
            usr = user_mentions[0]
            return Response("%s's id is `%s`" % (usr.name, usr.id), reply=True, delete_after=35)

    @owner_only
    async def cmd_joinserver(self, message, server_link=None):
        """
        Usage:
            !joinserver invite_link

        Asks the bot to join a server.  Note: Bot accounts cannot use invite links.
        """

        if self.user.bot:
            url = await self.generate_invite_link()
            return Response(
                "Bot accounts can't use invite links!  Click here to invite me: \n{}".format(url),
                reply=True, delete_after=30
            )

        try:
            if server_link:
                await self.accept_invite(server_link)
                return Response(":+1:")

        except:
            raise exceptions.CommandError('Invalid URL provided:\n{}\n'.format(server_link), expire_in=30)
    @owner_only
    async def cmd_pray(self, player, channel, author, message):
        '''
        Usage:
            !pray filepath
            Plays audio/video file on computer
            Breaks shit.
        '''
        filename = message.content.split()
        filename.pop(0)
        filename = " ".join(filename)
        try:
            await player.pray(_continue=False, filename=filename)
        except:
            print("ignoring errors")
    async def cmd_play(self, player, channel, author, server, permissions, leftover_args, song_url, Forced=False, mesag=None, ForcedAuthor=None):
        """
        Usage:
            !play song_link
            !play text to search for

        Adds the song to the playlist.  If a link is not provided, the first
        result from a youtube search is added to the queue.
        """
        if player.tts == 1:
            return Response("TTS is playing. You cannot queue music when TTS is playing.", delete_after=5)
        if not author.voice_channel:
            return Response("You have to be in a voice channel to queue music.", delete_after=10)
        for cnl in server.channels:
            for m in cnl.voice_members:
                if m.id == author.id:
                    if cnl.id != player.voice_client.channel.id:
                        return Response("You must be in the same voice channel as the bot to queue music.", delete_after=10)
        song_url = song_url.strip('<>')
        if not Forced and permissions.max_songs and player.playlist.count_for_user(author) >= permissions.max_songs:
            raise exceptions.PermissionsError(
                "You have reached your enqueued song limit (%s)" % permissions.max_songs, expire_in=30
            )
        if not Forced:
            await self.send_typing(channel)

        if leftover_args:
            song_url = ' '.join([song_url, *leftover_args])

        try:
            info = await self.downloader.extract_info(player.playlist.loop, song_url, download=False, process=False)
        except Exception as e:
            if not Forced:
                return Response("Either the video cannot be found or a massive error has occurred. Try again, and if it does not work, try again later. If it still does not work, notify an admin.", delete_after=20)
            else:
                return await self.edit_message(mesag, mesag.content+"\nI failed to find "+song_url)
            #raise exceptions.CommandError(e, expire_in=30)

        if not info:
            raise exceptions.CommandError("That video cannot be played.", expire_in=30)

        # abstract the search handling away from the user
        # our ytdl options allow us to use search strings as input urls
        if info.get('url', '').startswith('ytsearch'):
            # print("[Command:play] Searching for \"%s\"" % song_url)
            info = await self.downloader.extract_info(
                player.playlist.loop,
                song_url,
                download=False,
                process=True,    # ASYNC LAMBDAS WHEN
                on_error=lambda e: asyncio.ensure_future(
                    self.safe_send_message(channel, "```\nSomething is broken. Try again one more time and if it still doesn't work, tell an admin.\n```", expire_in=15), loop=self.loop),
                    #self.safe_send_message(channel, "```\n%s\n```" % e, expire_in=120), loop=self.loop),
                retry_on_error=True
            )

            if not info:
                raise exceptions.CommandError(
                    "Error extracting info from search string, youtubedl returned no data.  "
                    "You may need to restart the bot if this continues to happen.", expire_in=30
                )

            if not all(info.get('entries', [])):
                # empty list, no data
                return

            song_url = info['entries'][0]['webpage_url']
            info = await self.downloader.extract_info(player.playlist.loop, song_url, download=False, process=False)
            # Now I could just do: return await self.cmd_play(player, channel, author, song_url)
            # But this is probably fine

        # TODO: Possibly add another check here to see about things like the bandcamp issue
        # TODO: Where ytdl gets the generic extractor version with no processing, but finds two different urls

        if 'entries' in info:
            # I have to do exe extra checks anyways because you can request an arbitrary number of search results
            if not permissions.allow_playlists and ':search' in info['extractor'] and len(info['entries']) > 1:
                raise exceptions.PermissionsError("You are not allowed to request playlists", expire_in=30)

            # The only reason we would use this over `len(info['entries'])` is if we add `if _` to this one
            num_songs = sum(1 for _ in info['entries'])

            if permissions.max_playlist_length and num_songs > permissions.max_playlist_length:
                raise exceptions.PermissionsError(
                    "Playlist has too many entries (%s > %s)" % (num_songs, permissions.max_playlist_length),
                    expire_in=30
                )

            # This is a little bit weird when it says (x + 0 > y), I might add the other check back in
            if permissions.max_songs and player.playlist.count_for_user(author) + num_songs > permissions.max_songs:
                raise exceptions.PermissionsError(
                    "Playlist entries + your already queued songs reached limit (%s + %s > %s)" % (
                        num_songs, player.playlist.count_for_user(author), permissions.max_songs),
                    expire_in=30
                )

            if info['extractor'].lower() in ['youtube:playlist', 'soundcloud:set', 'bandcamp:album']:
                try:
                    return await self._cmd_play_playlist_async(player, channel, author, permissions, song_url, info['extractor'])
                except exceptions.CommandError:
                    raise
                except Exception as e:
                    traceback.print_exc()
                    raise exceptions.CommandError("Error queuing playlist:\n%s" % e, expire_in=30)

            t0 = time.time()

            # My test was 1.2 seconds per song, but we maybe should fudge it a bit, unless we can
            # monitor it and edit the message with the estimated time, but that's some ADVANCED SHIT
            # I don't think we can hook into it anyways, so this will have to do.
            # It would probably be a thread to check a few playlists and get the speed from that
            # Different playlists might download at different speeds though
            wait_per_song = 1.2

            procmesg = await self.safe_send_message(
                channel,
                'Gathering playlist information for {} songs{}'.format(
                    num_songs,
                    ', ETA: {} seconds'.format(self._fixg(
                        num_songs * wait_per_song)) if num_songs >= 10 else '.'))

            # We don't have a pretty way of doing this yet.  We need either a loop
            # that sends these every 10 seconds or a nice context manager.
            await self.send_typing(channel)

            # TODO: I can create an event emitter object instead, add event functions, and every play list might be asyncified
            #       Also have a "verify_entry" hook with the entry as an arg and returns the entry if its ok

            entry_list, position = await player.playlist.import_from(song_url, channel=channel, author=author)

            tnow = time.time()
            ttime = tnow - t0
            listlen = len(entry_list)
            drop_count = 0

            if permissions.max_song_length:
                for e in entry_list.copy():
                    if e.duration > permissions.max_song_length:
                        player.playlist.entries.remove(e)
                        entry_list.remove(e)
                        drop_count += 1
                        # Im pretty sure there's no situation where this would ever break
                        # Unless the first entry starts being played, which would make this a race condition
                if drop_count:
                    print("Dropped %s songs" % drop_count)

            print("Processed {} songs in {} seconds at {:.2f}s/song, {:+.2g}/song from expected ({}s)".format(
                listlen,
                self._fixg(ttime),
                ttime / listlen,
                ttime / listlen - wait_per_song,
                self._fixg(wait_per_song * num_songs))
            )

            await self.safe_delete_message(procmesg)

            if not listlen - drop_count:
                raise exceptions.CommandError(
                    "No songs were added, all songs were over max duration (%ss)" % permissions.max_song_length,
                    expire_in=30
                )

            reply_text = "Enqueued **%s** songs to be played. Position in queue: %s"
            btext = str(listlen - drop_count)

        else:
            if not Forced and permissions.max_song_length and info.get('duration', 0) > permissions.max_song_length:
                raise exceptions.PermissionsError(
                    "Song duration exceeds limit (%s > %s)" % (info['duration'], permissions.max_song_length),
                    expire_in=30
                )

            try:
                entry, position = await player.playlist.add_entry(song_url, channel=channel, author=ForcedAuthor)

            except exceptions.WrongEntryTypeError as e:
                if e.use_url == song_url:
                    print("[Warning] Determined incorrect entry type, but suggested url is the same.  Help.")

                if self.config.debug_mode:
                    print("[Info] Assumed url \"%s\" was a single entry, was actually a playlist" % song_url)
                    print("[Info] Using \"%s\" instead" % e.use_url)

                return await self.cmd_play(player, channel, author, permissions, leftover_args, e.use_url)

            reply_text = "Enqueued **%s** to be played. Position in queue: %s"
            btext = entry.title

        if position == 1 and player.is_stopped:
            position = 'Up next!'
            reply_text %= (btext, position)

        else:
            try:
                time_until = await player.playlist.estimate_time_until(position, player)
                reply_text += ' - estimated time until playing: %s'
            except:
                traceback.print_exc()
                time_until = ''
            try:
                reply_text %= (btext, position, time_until)
            except:
                reply_text = "There was an error somewhere. "+btext+" was queued. Everything should work fine."
        if not Forced:
            return Response(reply_text, delete_after=30)

    async def _cmd_play_playlist_async(self, player, channel, author, permissions, playlist_url, extractor_type):
        """
        Secret handler to use the async wizardry to make playlist queuing non-"blocking"
        """

        await self.send_typing(channel)
        info = await self.downloader.extract_info(player.playlist.loop, playlist_url, download=False, process=False)

        if not info:
            raise exceptions.CommandError("That playlist cannot be played.")

        num_songs = sum(1 for _ in info['entries'])
        t0 = time.time()

        busymsg = await self.safe_send_message(
            channel, "Processing %s songs..." % num_songs)  # TODO: From playlist_title
        await self.send_typing(channel)

        entries_added = 0
        if extractor_type == 'youtube:playlist':
            try:
                entries_added = await player.playlist.async_process_youtube_playlist(
                    playlist_url, channel=channel, author=author)
                # TODO: Add hook to be called after each song
                # TODO: Add permissions

            except Exception:
                traceback.print_exc()
                raise exceptions.CommandError('Error handling playlist %s queuing.' % playlist_url, expire_in=30)

        elif extractor_type.lower() in ['soundcloud:set', 'bandcamp:album']:
            try:
                entries_added = await player.playlist.async_process_sc_bc_playlist(
                    playlist_url, channel=channel, author=author)
                # TODO: Add hook to be called after each song
                # TODO: Add permissions

            except Exception:
                traceback.print_exc()
                raise exceptions.CommandError('Error handling playlist %s queuing.' % playlist_url, expire_in=30)


        songs_processed = len(entries_added)
        drop_count = 0
        skipped = False

        if permissions.max_song_length:
            for e in entries_added.copy():
                if e.duration > permissions.max_song_length:
                    try:
                        player.playlist.entries.remove(e)
                        entries_added.remove(e)
                        drop_count += 1
                    except:
                        pass

            if drop_count:
                print("Dropped %s songs" % drop_count)

            if player.current_entry and player.current_entry.duration > permissions.max_song_length:
                await self.safe_delete_message(self.server_specific_data[channel.server]['last_np_msg'])
                self.server_specific_data[channel.server]['last_np_msg'] = None
                skipped = True
                player.skip()
                entries_added.pop()

        await self.safe_delete_message(busymsg)

        songs_added = len(entries_added)
        tnow = time.time()
        ttime = tnow - t0
        wait_per_song = 1.2
        # TODO: actually calculate wait per song in the process function and return that too

        # This is technically inaccurate since bad songs are ignored but still take up time
        print("Processed {}/{} songs in {} seconds at {:.2f}s/song, {:+.2g}/song from expected ({}s)".format(
            songs_processed,
            num_songs,
            self._fixg(ttime),
            ttime / num_songs,
            ttime / num_songs - wait_per_song,
            self._fixg(wait_per_song * num_songs))
        )

        if not songs_added:
            basetext = "No songs were added, all songs were over max duration (%ss)" % permissions.max_song_length
            if skipped:
                basetext += "\nAdditionally, the current song was skipped for being too long."

            raise exceptions.CommandError(basetext, expire_in=30)

        return Response("Enqueued {} songs to be played in {} seconds".format(
            songs_added, self._fixg(ttime, 1)), delete_after=30)

    async def cmd_search(self, player, channel, author, permissions, leftover_args):
        """
        Usage:
            !search [service] [number] query

        Searches a service for a video and adds it to the queue.
        - service: any one of the following services:
            - youtube (yt) (default if unspecified)
            - soundcloud (sc)
            - yahoo (yh)
        - number: return a number of video results and waits for user to choose one
          - defaults to 1 if unspecified
          - note: If your search query starts with a number,
                  you must put your query in quotes
            - ex: {command_prefix}search 2 "I ran seagulls"
        """

        if permissions.max_songs and player.playlist.count_for_user(author) > permissions.max_songs:
            raise exceptions.PermissionsError(
                "You have reached your playlist item limit (%s)" % permissions.max_songs,
                expire_in=30
            )

        def argcheck():
            if not leftover_args:
                raise exceptions.CommandError(
                    "Please specify a search query.\n%s" % dedent(
                        self.cmd_search.__doc__.format(command_prefix=self.config.command_prefix)),
                    expire_in=60
                )

        argcheck()

        try:
            leftover_args = shlex.split(' '.join(leftover_args))
        except ValueError:
            raise exceptions.CommandError("Please quote your search query properly.", expire_in=30)

        service = 'youtube'
        items_requested = 3
        max_items = 10  # this can be whatever, but since ytdl uses about 1000, a small number might be better
        services = {
            'youtube': 'ytsearch',
            'soundcloud': 'scsearch',
            'yahoo': 'yvsearch',
            'yt': 'ytsearch',
            'sc': 'scsearch',
            'yh': 'yvsearch'
        }

        if leftover_args[0] in services:
            service = leftover_args.pop(0)
            argcheck()

        if leftover_args[0].isdigit():
            items_requested = int(leftover_args.pop(0))
            argcheck()

            if items_requested > max_items:
                raise exceptions.CommandError("You cannot search for more than %s videos" % max_items)

        # Look jake, if you see this and go "what the fuck are you doing"
        # and have a better idea on how to do this, i'd be delighted to know.
        # I don't want to just do ' '.join(leftover_args).strip("\"'")
        # Because that eats both quotes if they're there
        # where I only want to eat the outermost ones
        if leftover_args[0][0] in '\'"':
            lchar = leftover_args[0][0]
            leftover_args[0] = leftover_args[0].lstrip(lchar)
            leftover_args[-1] = leftover_args[-1].rstrip(lchar)

        search_query = '%s%s:%s' % (services[service], items_requested, ' '.join(leftover_args))

        search_msg = await self.send_message(channel, "Searching for videos...")
        await self.send_typing(channel)

        try:
            info = await self.downloader.extract_info(player.playlist.loop, search_query, download=False, process=True)

        except Exception as e:
            await self.safe_edit_message(search_msg, str(e), send_if_fail=True)
            return
        else:
            await self.safe_delete_message(search_msg)

        if not info:
            return Response("No videos found.", delete_after=30)

        def check(m):
            return (
                m.content.lower()[0] in 'yn' or
                # hardcoded function name weeee
                m.content.lower().startswith('{}{}'.format(self.config.command_prefix, 'search')) or
                m.content.lower().startswith('exit'))

        for e in info['entries']:
            result_message = await self.safe_send_message(channel, "Result %s/%s: %s" % (
                info['entries'].index(e) + 1, len(info['entries']), e['webpage_url']))

            confirm_message = await self.safe_send_message(channel, "Is this ok? Type `y`, `n` or `exit`")
            response_message = await self.wait_for_message(30, author=author, channel=channel, check=check)

            if not response_message:
                await self.safe_delete_message(result_message)
                await self.safe_delete_message(confirm_message)
                return Response("Ok nevermind.", delete_after=30)

            # They started a new search query so lets clean up and bugger off
            elif response_message.content.startswith(self.config.command_prefix) or \
                    response_message.content.lower().startswith('exit'):

                await self.safe_delete_message(result_message)
                await self.safe_delete_message(confirm_message)
                return

            if response_message.content.lower().startswith('y'):
                await self.safe_delete_message(result_message)
                await self.safe_delete_message(confirm_message)
                await self.safe_delete_message(response_message)

                await self.cmd_play(player, channel, author, permissions, [], e['webpage_url'])

                return Response("Alright, coming right up!", delete_after=30)
            else:
                await self.safe_delete_message(result_message)
                await self.safe_delete_message(confirm_message)
                await self.safe_delete_message(response_message)

        return Response("Oh well :frowning:", delete_after=30)

    async def cmd_np(self, player, channel, server, message):
        """
        Usage:
            !np

        Displays the current song in chat.
        """

        if player.current_entry:
            if self.server_specific_data[server]['last_np_msg']:
                await self.safe_delete_message(self.server_specific_data[server]['last_np_msg'])
                self.server_specific_data[server]['last_np_msg'] = None

            song_progress = str(timedelta(seconds=player.progress)).lstrip('0').lstrip(':')
            song_total = str(timedelta(seconds=player.current_entry.duration)).lstrip('0').lstrip(':')
            prog_str = '`[%s/%s]`' % (song_progress, song_total)

            if player.current_entry.meta.get('channel', False) and player.current_entry.meta.get('author', False):
                np_text = "Now Playing: **%s** added by **%s** %s\n" % (
                    player.current_entry.title, player.current_entry.meta['author'].name, prog_str)
            else:
                np_text = "Now Playing: **%s** %s\n" % (player.current_entry.title, prog_str)

            self.server_specific_data[server]['last_np_msg'] = await self.safe_send_message(channel, np_text)
            await self._manual_delete_check(message)
        else:
            return Response(
                'There are no songs queued! Queue something with {}play.'.format(self.config.command_prefix),
                delete_after=30
            )

    async def cmd_summon(self, channel, author, voice_channel):
        """
        Usage:
            !summon

        Call the bot to the summoner's voice channel.
        """

        if not author.voice_channel:
            raise exceptions.CommandError('You are not in a voice channel!')

        voice_client = self.the_voice_clients.get(channel.server.id, None)
        if voice_client and voice_client.channel.server == author.voice_channel.server:
            await self.move_voice_client(author.voice_channel)
            return

        # move to _verify_vc_perms?
        chperms = author.voice_channel.permissions_for(author.voice_channel.server.me)

        if not chperms.connect:
            self.safe_print("Cannot join channel \"%s\", no permission." % author.voice_channel.name)
            return Response(
                "```Cannot join channel \"%s\", no permission.```" % author.voice_channel.name,
                delete_after=25
            )

        elif not chperms.speak:
            self.safe_print("Will not join channel \"%s\", no permission to speak." % author.voice_channel.name)
            return Response(
                "```Will not join channel \"%s\", no permission to speak.```" % author.voice_channel.name,
                delete_after=25
            )

        player = await self.get_player(author.voice_channel, create=True)

        if player.is_stopped:
            player.play()

        if self.config.auto_playlist:
            await self.on_player_finished_playing(player)

    async def cmd_pause(self, player):
        """
        Usage:
            !pause

        Pauses playback of the current song.
        """

        if player.is_playing:
            player.pause()

        else:
            raise exceptions.CommandError('Player is not playing.', expire_in=30)

    async def cmd_resume(self, player):
        """
        Usage:
            !resume

        Resumes playback of a paused song.
        """

        if player.is_paused:
            player.resume()

        else:
            raise exceptions.CommandError('Player is not paused.', expire_in=30)

    async def cmd_shuffle(self, channel, player):
        """
        Usage:
            !shuffle

        Shuffles the playlist.
        """

        player.playlist.shuffle()

        cards = [':spades:',':clubs:',':hearts:',':diamonds:']
        hand = await self.send_message(channel, ' '.join(cards))
        await asyncio.sleep(0.6)

        for x in range(4):
            shuffle(cards)
            await self.safe_edit_message(hand, ' '.join(cards))
            await asyncio.sleep(0.6)

        await self.safe_delete_message(hand, quiet=True)
        return Response(":ok_hand:", delete_after=15)

    async def cmd_clear(self, player, author):
        """
        Usage:
            !clear

        Clears the playlist.
        """

        player.playlist.clear()
        return Response('RIP Playlist :sunglasses: :ok_hand:', delete_after=20)

    async def cmd_skip(self, player, channel, author, message, permissions, voice_channel):
        """
        Usage:
            !skip

        Skips the current song when enough votes are cast, or by the bot owner.
        """

        if player.is_stopped:
            raise exceptions.CommandError("Can't skip! The player is not playing!", expire_in=20)

        if not player.current_entry:
            if player.playlist.peek():
                if player.playlist.peek()._is_downloading:
                    # print(player.playlist.peek()._waiting_futures[0].__dict__)
                    return Response("The next song (%s) is downloading, please wait." % player.playlist.peek().title)

                elif player.playlist.peek().is_downloaded:
                    print("The next song will be played shortly.  Please wait.")
                else:
                    print("Something odd is happening.  "
                          "You might want to restart the bot if it doesn't start working.")
            else:
                print("Something strange is happening.  "
                      "You might want to restart the bot if it doesn't start working.")

        if author.id == self.config.owner_id \
                or permissions.instaskip \
                or author == player.current_entry.meta.get('author', None):

            player.skip()  # check autopause stuff here
            await self._manual_delete_check(message)
            try:
                print(player.current_entry.title)
                addmsg = ""
            except:
                addmsg = "The playlist is empty or the next song is downloading."
            if permissions.instaskip:
                return Response("skipped the song using mod override... "+addmsg, reply=True, delete_after=10)
            if author.id == self.config.owner_id:
                return Response("skipped the song using owner override... "+addmsg, reply=True, delete_after=10)
            if author == player.current_entry.meta.get('author', None):
                return Response("skipped the song using queuer override... "+addmsg, reply=True, delete_after=10)
        # TODO: ignore person if they're deaf or take them out of the list or something?
        # Currently is recounted if they vote, deafen, then vote

        num_voice = sum(1 for m in voice_channel.voice_members if not (
            m.deaf or m.self_deaf or m.id in [self.config.owner_id, self.user.id]))

        num_skips = player.skip_state.add_skipper(author.id, message)

        skips_remaining = min(self.config.skips_required,
                              sane_round_int(num_voice * self.config.skip_ratio_required)) - num_skips

        if skips_remaining <= 0:
            player.skip()  # check autopause stuff here
            try:
                print(player.current_entry.title)
            except:
                return Response("your skip was acknowledged.\nThe song has been skipped.\nEither the playlist is empty or the next song is downloading.", reply=True, delete_after=10)
            return Response(
                'your skip for **{}** was acknowledged.'
                '\nThe vote to skip has been passed.{}'.format(
                    player.current_entry.title,
                    ' Next song coming up!' if player.playlist.peek() else ''
                ),
                reply=True,
                delete_after=20
            )

        else:
            # TODO: When a song gets skipped, delete the old x needed to skip messages
            try:
                print(player.current_entry.title)
            except:
                return Response("your skip was acknowledged.\nThe song needs more votes to be skipped.\nSomething went wrong during this command.", reply=True, delete_after=10)
            return Response(
                'your skip for **{}** was acknowledged.'
                '\n**{}** more {} required to vote to skip this song.'.format(
                    player.current_entry.title,
                    skips_remaining,
                    'person is' if skips_remaining == 1 else 'people are'
                ),
                reply=True,
                delete_after=20
            )
    @owner_only
    async def cmd_lockvolume(self, message, author):
        '''
        Toggles !volume lock
        '''
        global lockedvolume
        if lockedvolume == 1:
            lockedvolume = 0
        else:
            lockedvolume = 1
        return Response("Toggled", delete_after=2)
    @owner_only
    async def cmd_forcevol(self, message, author, player):
        '''
        Usage:
            !forcevol number
            Forces !volume beyond 100%. Takes any number. 1 = 100.
        '''
        msg = message.content.strip().split()
        msg.pop(0)
        newvol = msg[0]
        player.volume = float(newvol)
    async def cmd_volume(self, message, player, permissions, new_volume=None):
        """
        Usage:
            !volume (+/-)[volume]

        Sets the playback volume. Accepted values are from 1 to 100.
        Putting + or - before the volume will make the volume change relative to the current volume.
        """
        global lockedvolume
        if lockedvolume == 1:
            return Response("Cannot change volume: It is locked.", delete_after=5)
        if not new_volume:
            return Response('Current volume: `%s%%`' % int(player.volume * 100), reply=True, delete_after=20)

        relative = False
        if new_volume[0] in '+-':
            relative = True

        try:
            new_volume = int(new_volume)

        except ValueError:
            raise exceptions.CommandError('{} is not a valid number'.format(new_volume), expire_in=20)

        if relative:
            vol_change = new_volume
            new_volume += (player.volume * 100)

        old_volume = int(player.volume * 100)

        if abs(old_volume - new_volume) > 60:
            if permissions.volumeoverride or message.author.id == "104461925009608704":
                print("Admin bypass used")
            else:
                raise exceptions.CommandError("You attempted to change the volume by too dramatic an amount; more than 60.", expire_in=10)
            
        if 0 < new_volume <= 100:
            player.volume = new_volume / 100.0

            return Response('updated volume from %d to %d' % (old_volume, new_volume), reply=True, delete_after=20)

        else:
            if relative:
                raise exceptions.CommandError(
                    'Unreasonable volume change provided: {}{:+} -> {}%.  Provide a change between {} and {:+}.'.format(
                        old_volume, vol_change, old_volume + vol_change, 1 - old_volume, 100 - old_volume), expire_in=20)
            else:
                raise exceptions.CommandError(
                    'Unreasonable volume provided: {}%. Provide a value between 1 and 100.'.format(new_volume), expire_in=20)
    async def cmd_playlist(self, channel, player):
        '''
        Usage:
            !playlist
            
        This is an alias for !queue.
        Prints the current song playlist.
        '''
        lines = []
        unlisted = 0
        andmoretext = '* ... and %s more*' % ('x' * len(player.playlist.entries))

        if player.current_entry:
            song_progress = str(timedelta(seconds=player.progress)).lstrip('0').lstrip(':')
            song_total = str(timedelta(seconds=player.current_entry.duration)).lstrip('0').lstrip(':')
            prog_str = '`[%s/%s]`' % (song_progress, song_total)

            if player.current_entry.meta.get('channel', False) and player.current_entry.meta.get('author', False):
                lines.append("Now Playing: **%s** added by **%s** %s\n" % (
                    player.current_entry.title, player.current_entry.meta['author'].name, prog_str))
            else:
                lines.append("Now Playing: **%s** %s\n" % (player.current_entry.title, prog_str))

        for i, item in enumerate(player.playlist, 1):
            if item.meta.get('channel', False) and item.meta.get('author', False):
                nextline = '`{}.` **{}** added by **{}**'.format(i, item.title, item.meta['author'].name).strip()
            else:
                nextline = '`{}.` **{}**'.format(i, item.title).strip()

            currentlinesum = sum(len(x) + 1 for x in lines)  # +1 is for newline char

            if currentlinesum + len(nextline) + len(andmoretext) > DISCORD_MSG_CHAR_LIMIT:
                if currentlinesum + len(andmoretext):
                    unlisted += 1
                    continue

            lines.append(nextline)

        if unlisted:
            lines.append('\n*... and %s more*' % unlisted)

        if not lines:
            lines.append(
                'There are no songs queued! Queue something with {}play.'.format(self.config.command_prefix))

        message = '\n'.join(lines)
        return Response(message, delete_after=30)
    async def cmd_queue(self, channel, player):
        """
        Usage:
            !queue

        Prints the current song queue.
        """

        lines = []
        unlisted = 0
        andmoretext = '* ... and %s more*' % ('x' * len(player.playlist.entries))

        if player.current_entry:
            song_progress = str(timedelta(seconds=player.progress)).lstrip('0').lstrip(':')
            song_total = str(timedelta(seconds=player.current_entry.duration)).lstrip('0').lstrip(':')
            prog_str = '`[%s/%s]`' % (song_progress, song_total)

            if player.current_entry.meta.get('channel', False) and player.current_entry.meta.get('author', False):
                lines.append("Now Playing: **%s** added by **%s** %s\n" % (
                    player.current_entry.title, player.current_entry.meta['author'].name, prog_str))
            else:
                lines.append("Now Playing: **%s** %s\n" % (player.current_entry.title, prog_str))

        for i, item in enumerate(player.playlist, 1):
            if item.meta.get('channel', False) and item.meta.get('author', False):
                nextline = '`{}.` **{}** added by **{}**'.format(i, item.title, item.meta['author'].name).strip()
            else:
                nextline = '`{}.` **{}**'.format(i, item.title).strip()

            currentlinesum = sum(len(x) + 1 for x in lines)  # +1 is for newline char

            if currentlinesum + len(nextline) + len(andmoretext) > DISCORD_MSG_CHAR_LIMIT:
                if currentlinesum + len(andmoretext):
                    unlisted += 1
                    continue

            lines.append(nextline)

        if unlisted:
            lines.append('\n*... and %s more*' % unlisted)

        if not lines:
            lines.append(
                'There are no songs queued! Queue something with {}play.'.format(self.config.command_prefix))

        message = '\n'.join(lines)
        return Response(message, delete_after=30)

    async def cmd_clean(self, message, channel, server, author, search_range=50):
        """
        Usage:
            !clean [range]

        Removes up to [range] messages the bot has posted in chat. Default: 50, Max: 1000
        """

        try:
            float(search_range)  # lazy check
            search_range = min(int(search_range), 1000)
        except:
            return Response("enter a number.  NUMBER.  That means digits.  `15`.  Etc.", reply=True, delete_after=8)

        await self.safe_delete_message(message, quiet=True)

        def is_possible_command_invoke(entry):
            valid_call = any(
                entry.content.startswith(prefix) for prefix in [self.config.command_prefix])  # can be expanded
            return valid_call and not entry.content[1:2].isspace()

        delete_invokes = True
        delete_all = channel.permissions_for(author).manage_messages or self.config.owner_id == author.id

        def check(message):
            if is_possible_command_invoke(message) and delete_invokes:
                return delete_all or message.author == author
            return message.author == self.user

        if self.user.bot:
            if channel.permissions_for(server.me).manage_messages:
                deleted = await self.purge_from(channel, check=check, limit=search_range, before=message)
                return Response('Cleaned up {} message{}.'.format(len(deleted), 's' * bool(deleted)), delete_after=15)

        deleted = 0
        async for entry in self.logs_from(channel, search_range, before=message):
            if entry == self.server_specific_data[channel.server]['last_np_msg']:
                continue

            if entry.author == self.user:
                await self.safe_delete_message(entry)
                deleted += 1
                await asyncio.sleep(0.21)

            if is_possible_command_invoke(entry) and delete_invokes:
                if delete_all or entry.author == author:
                    try:
                        await self.delete_message(entry)
                        await asyncio.sleep(0.21)
                        deleted += 1

                    except discord.Forbidden:
                        delete_invokes = False
                    except discord.HTTPException:
                        pass

        return Response('Cleaned up {} message{}.'.format(deleted, 's' * bool(deleted)), delete_after=15)

    async def cmd_pldump(self, channel, song_url):
        """
        Usage:
            !pldump url

        Dumps the individual urls of a playlist
        """

        try:
            info = await self.downloader.extract_info(self.loop, song_url.strip('<>'), download=False, process=False)
        except Exception as e:
            raise exceptions.CommandError("Could not extract info from input url\n%s\n" % e, expire_in=25)

        if not info:
            raise exceptions.CommandError("Could not extract info from input url, no data.", expire_in=25)

        if not info.get('entries', None):
            # TODO: Retarded playlist checking
            # set(url, webpageurl).difference(set(url))

            if info.get('url', None) != info.get('webpage_url', info.get('url', None)):
                raise exceptions.CommandError("This does not seem to be a playlist.", expire_in=25)
            else:
                return await self.cmd_pldump(channel, info.get(''))

        linegens = defaultdict(lambda: None, **{
            "youtube":    lambda d: 'https://www.youtube.com/watch?v=%s' % d['id'],
            "soundcloud": lambda d: d['url'],
            "bandcamp":   lambda d: d['url']
        })

        exfunc = linegens[info['extractor'].split(':')[0]]

        if not exfunc:
            raise exceptions.CommandError("Could not extract info from input url, unsupported playlist type.", expire_in=25)

        with BytesIO() as fcontent:
            for item in info['entries']:
                fcontent.write(exfunc(item).encode('utf8') + b'\n')

            fcontent.seek(0)
            await self.send_file(channel, fcontent, filename='playlist.txt', content="Here's the url dump for <%s>" % song_url)

        return Response(":mailbox_with_mail:", delete_after=20)

    async def cmd_listids(self, server, author, leftover_args, cat='all'):
        """
        Usage:
            !listids [categories]

        Lists the ids for various things.  Categories are:
           all, users, roles, channels
        """

        cats = ['channels', 'roles', 'users']

        if cat not in cats and cat != 'all':
            return Response(
                "Valid categories: " + ' '.join(['`%s`' % c for c in cats]),
                reply=True,
                delete_after=25
            )

        if cat == 'all':
            requested_cats = cats
        else:
            requested_cats = [cat] + [c.strip(',') for c in leftover_args]

        data = ['Your ID: %s' % author.id]

        for cur_cat in requested_cats:
            rawudata = None

            if cur_cat == 'users':
                data.append("\nUser IDs:")
                rawudata = ['%s #%s: %s' % (m.name, m.discriminator, m.id) for m in server.members]

            elif cur_cat == 'roles':
                data.append("\nRole IDs:")
                rawudata = ['%s: %s' % (r.name, r.id) for r in server.roles]

            elif cur_cat == 'channels':
                data.append("\nText Channel IDs:")
                tchans = [c for c in server.channels if c.type == discord.ChannelType.text]
                rawudata = ['%s: %s' % (c.name, c.id) for c in tchans]

                rawudata.append("\nVoice Channel IDs:")
                vchans = [c for c in server.channels if c.type == discord.ChannelType.voice]
                rawudata.extend('%s: %s' % (c.name, c.id) for c in vchans)

            if rawudata:
                data.extend(rawudata)

        with BytesIO() as sdata:
            sdata.writelines(d.encode('utf8') + b'\n' for d in data)
            sdata.seek(0)

            # TODO: Fix naming (Discord20API-ids.txt)
            await self.send_file(author, sdata, filename='%s-ids-%s.txt' % (server.name.replace(' ', '_'), cat))

        return Response(":mailbox_with_mail:", delete_after=20)


    async def cmd_perms(self, author, channel, server, permissions):
        """
        Usage:
            !perms

        Sends the user a list of their permissions.
        """

        lines = ['Command permissions in %s\n' % server.name, '```', '```']

        for perm in permissions.__dict__:
            if perm in ['user_list'] or permissions.__dict__[perm] == set():
                continue

            lines.insert(len(lines) - 1, "%s: %s" % (perm, permissions.__dict__[perm]))

        await self.send_message(author, '\n'.join(lines))
        return Response(":mailbox_with_mail:", delete_after=20)


    @owner_only
    async def cmd_setname(self, leftover_args, name):
        """
        Usage:
            !setname name

        Changes the bot's username.
        Note: This operation is limited by discord to twice per hour.
        """

        name = ' '.join([name, *leftover_args])

        try:
            await self.edit_profile(username=name)
        except Exception as e:
            raise exceptions.CommandError(e, expire_in=20)

        return Response(":ok_hand:", delete_after=20)

    @owner_only
    async def cmd_setnick(self, server, channel, leftover_args, nick):
        """
        Usage:
            !setnick nick

        Changes the bot's nickname.
        """

        if not channel.permissions_for(server.me).change_nickname:
            raise exceptions.CommandError("Unable to change nickname: no permission.")

        nick = ' '.join([nick, *leftover_args])

        try:
            await self.change_nickname(server.me, nick)
        except Exception as e:
            raise exceptions.CommandError(e, expire_in=20)

        return Response(":ok_hand:", delete_after=20)

    @owner_only
    async def cmd_setavatar(self, message, url=None):
        """
        Usage:
            !setavatar [url]

        Changes the bot's avatar.
        Attaching a file and leaving the url parameter blank also works.
        """

        if message.attachments:
            thing = message.attachments[0]['url']
        else:
            thing = url.strip('<>')

        try:
            with aiohttp.Timeout(10):
                async with self.aiosession.get(thing) as res:
                    await self.edit_profile(avatar=await res.read())

        except Exception as e:
            raise exceptions.CommandError("Unable to change avatar: %s" % e, expire_in=20)

        return Response(":ok_hand:", delete_after=20)
        
        
    async def cmd_chroles(self, server, channel, message, author, user_mentions):
        """
        Usage:
            !chroles @user Role1[, Role2, Role3, Role4, ...]
            
        Replaces @user's roles by removing all previous roles and replacing them with the list you give.
        At least 1 role is required. Separate roles with commas.
        """
        leftargs = message.content.split()
        if len(leftargs) < 3:
            return Response("```Usage:\n    !chroles @user Role1[, Role2, Role3, Role4, ...]\n\nReplaces @user's roles.\nAt least 1 role is required. Separate roles with commas.```", delete_after=5)
        leftargs.pop(0)
        leftargs.pop(0)
        msg = " ".join(leftargs)
        roles = msg.split(",")
        roleobjs = []
        realrolesnames = []
        realroles = []
        for i in range(len(server.roles)):
            realroles.append(server.roles[i])
        for i in range(len(server.roles)):
            realrolesnames.append(server.roles[i].name.lower())
        for i in range(len(roles)):
            roles[i] = roles[i].strip(" ")
        print(roles)
        print(realrolesnames)
        print(realroles)
        for i in range(len(roles)):
            if roles[i].lower() not in realrolesnames:
                return Response("One of the roles you tried to add does not exist. Try again.", delete_after=10)
            roleobjs.append(realroles[realrolesnames.index(roles[i].lower())])
        print(roleobjs)
        await self.replace_roles(user_mentions[0], *roleobjs)
        return Response("i tried :joy:", delete_after=20)
    async def cmd_makesub(self, server, channel, message, author):
        '''
        Usage:
            !makesub [rolename]
            Creates a new role by the rolename for use in the news role list.
            Subscribe with !sub [rolename]. View a list with !newsroles.
        '''
        params = message.content.strip().split()
        params.pop(0)
        try:
            params[0] = " ".join(params)
        except:
            return Response("You must include a role.", delete_after=5)
        for role in server.roles:
            if role.name.lower() == params[0].lower():
                return Response("This role already exists.", delete_after=15)
        perms = discord.Permissions(permissions=0)
        await self.create_role(server, name=params[0], permissions=perms, mentionable=True)
        await self.send_message(channel, "I've made a new sublist called "+params[0])
        
    async def cmd_delsub(self, server, channel, message, author):
        '''
        Usage:
            !delsub [rolename]
            Deletes an entire news role from the role list. It is gone forever.
        '''
        params = message.content.strip().split()
        params.pop(0)
        try:
            params[0] = " ".join(params)
        except:
            return Response("You must include a role.", delete_after=5)
        delrole = None
        for role in server.roles:
            if role.name == "vv News Roles vv":
                roleline = role
        for role in server.roles:
            if role.name.lower() == params[0].lower() or role.mention == params[0]:
                delrole = role
        if delrole == None:
            return Response("That role doesn't exist.", delete_after=5)
        if delrole >= roleline:
            return Response("You can't delete those roles.", delete_after=10)
        await self.delete_role(server, delrole)
        await self.send_message(channel, "I have deleted the sublist "+delrole.name)
        
    async def cmd_sub(self, server, channel, message, author, permissions, user_mentions):
        '''
        Usage:
            !sub role [@user]
            Subscribe to a game news role list (assign it as one of your roles).
            The role does not have to be a mention, but the @user does.
            !newsroles for the list of roles.
        '''
        params = message.content.strip().split()
        params.pop(0)
        try:
            params = " ".join(params).split("<@")
            params[0] = params[0].strip()
        except:
            return Response("You must include a role.", delete_after=5)
        subrole = None
        for role in server.roles:
            if role.mention == params[0] or role.name.lower() == params[0].lower():
                # role found
                subrole = role
            if role.name == "vv News Roles vv":
                roleline = role
        if subrole == None:
            return Response("This role does not exist.", delete_after=5)
        if subrole >= roleline:
            return Response("That probably isn't a news-related role... Try again.", delete_after=10)
        if server.name != "Ghost Division":
            return Response("This command does not work in this server.", delete_after=10)
        if user_mentions:
            if self.permissions.for_user(author).name in ["Owner (auto)", "Admin", "Moderator"]:
                winner = user_mentions[0]
            else:
                if user_mentions[0] == author:
                    winner = user_mentions[0]
                else:
                    return Response("You don't have permission to sub other people to a news role.", delete_after=10)
        else:
            winner = author
        for role in winner.roles:
            if subrole == role:
                return Response(winner.name+" is already subscribed to this mention list.", delete_after=15)
        await self.add_roles(winner, subrole)
        return Response("You have subscribed "+winner.name+" to the "+subrole.name+" mention list.", delete_after=15)
        
    async def cmd_newsroles(self, server, channel, message, author, user_mentions):
        '''
        Just returns the list of newsroles.
        '''
        rolelist = []
        for role in server.roles:
            if role.name == "vv News Roles vv":
                roleline = role
        for role in server.roles:
            if role < roleline and role.name != "@everyone":
                rolelist.append(role.name)
        await self.send_message(channel, "Here is a list of the news-related roles:\n```\n"+"\n".join(rolelist)+"```")
        
    async def cmd_unsub(self, server, channel, message, author, user_mentions):
        '''
        Usage:
            !unsub role [@user]
            Unsubscribe to a game news role list (unassign it from your roles).
            The role does not have to be a mention, but the @user does.
            !newsroles for the list of roles.
        '''
        params = message.content.strip().split()
        params.pop(0)
        try:
            params = " ".join(params).split("<@")
            params[0] = params[0].strip()
        except:
            return Response("You must include a role.", delete_after=5)
        subrole = None
        for role in server.roles:
            if role.mention == params[0] or role.name.lower() == params[0].lower():
                subrole = role
            if role.name == "vv News Roles vv":
                roleline = role
        if subrole == None:
            return Response("This role does not exist.", delete_after=5)
        if subrole >= roleline:
            return Response("That probably isn't a news-related role... Try again.", delete_after=10)
        if server.name != "Ghost Division":
            return Response("This command does not work in this server.", delete_after=10)
        confirmation = None
        if user_mentions:
            if self.permissions.for_user(author).name in ["Owner (auto)", "Admin", "Moderator"]:
                loser = user_mentions[0]
            else:
                if user_mentions[0] == author:
                    loser = user_mentions[0]
                else:
                    return Response("You don't have permission to unsub other people from a news role.", delete_after=10)
        else:
            loser = author
        for role in loser.roles:
            if subrole == role:
                confirmation = "yes"
                await self.remove_roles(loser, subrole)
        if confirmation == None:
            return Response(loser.name+" is not a member of this mention list.", delete_after=10)
        return Response("You have unsubscribed "+loser.name+" from the "+subrole.name+" mention list.", delete_after=15)
        
    async def cmd_emptyrole(self, server, channel, message, author, user_mentions):
        '''
        Usage:
            !emptyrole [role]
            Remove everyone in the server from a role. Useful for news lists.
            This works with or without the @.
        '''
        params = message.content.strip().split()
        params.pop(0)
        try:
            params[0] = " ".join(params)
        except:
            return Response("You must include a role.", delete_after=5)
        emptyrole = None
        for role in server.roles:
            if role.mention == params[0] or role.name.lower() == params[0].lower():
                emptyrole = role
        if emptyrole == None:
            return Response("This role does not exist.", delete_after=10)
        if emptyrole.name == "@everyone":
            return Response("That's not possible.", delete_after=10)
        for member in server.members:
            for role in member.roles:
                if role == emptyrole:
                    await self.remove_roles(member, emptyrole)
        return Response("The role "+emptyrole.name+" is now empty.", delete_after=15)
        
    async def cmd_listsubs(self, server, channel, message, author, user_mentions):
        '''
        Usage:
            !listsubs [role]
            See the full list of people subscribed to a news role.
            !newsroles for the list of roles.
            (This works on any role.)
        '''
        params = message.content.strip().split()
        params.pop(0)
        try:
            params[0] = " ".join(params)
        except:
            return Response("You must include a role.", delete_after=5)
        chkrole = None
        for role in server.roles:
            if role.mention == params[0] or role.name.lower() == params[0].lower():
                chkrole = role
        if chkrole == None:
            return Response("This role does not exist.", delete_after=10)
        if chkrole.name == "@everyone":
            return Response("That's everyone...", delete_after=10)
        memberlist = []
        for member in server.members:
            for role in member.roles:
                if role == chkrole:
                    memberlist.append(member.name)
        await self.send_message(channel, "Here is a list of the members of that role:\n```\n"+"\n".join(memberlist)+"```")
        
    @owner_only
    async def cmd_cleanroles(self, server): #remove all roles except highest from a person
        return ""
    
    async def cmd_kys(self, server):
        '''
        Removes the bot from voice chat.
        '''
        await self.disconnect_voice_client(server)
        return Response(":hear_no_evil:", delete_after=20)

    async def cmd_restart(self, channel):
        '''
        Restarts the bot. Stops cleaning up of messages. Only refreshes the bot, does not reload python files.
        '''
        await self.safe_send_message(channel, "I will return fam :100:")
        await self.disconnect_all_voice_clients()
        raise exceptions.RestartSignal

    async def cmd_shutdown(self, channel):
        '''
        Shuts down the bot. Bot does not restart.
        '''
        await self.safe_send_message(channel, ":ok_hand: :joy: :gun:")
        await self.disconnect_all_voice_clients()
        global timerun_barsaver
        raise exceptions.TerminateSignal
		
    async def cmd_lemao(self, channel):
        '''
        xDDDDDDD
        '''
        return Response("LMAO MY FUCKING ASS OFF :100: :100: :ok_hand: :joy:", delete_after=2)

        
        
        
        
#   unotable[0][0] = channel name
#   unotable[0][1] = channel object
#   unotable[1][0] = reverse flag (true = normal play)
#   unotable[1][1] = whether or not the game is going on (1 = True)
#   unotable[1][2] = the passflag (for !pass)
#   unotable[1][3] = tempflag for !makeuno reuse
#   unotable[1][4] = number of times !draw was used
#   unotable[1][5] = the quit/endflag (for !quituno and !stopgame)
#   unotable[1][6] = whether or not the bot is in the game
#   unotable[2][0] = turn number (not to exceed number of players)
#   unotable[3][0] = number of players - 1
#   unotable[4] = dictionary of each player and their cards
#   unotable[5]    = an array of strings of players in the order they should be (so when turn=0, unotable[5][0] is the person to play)
#   unotable[6]    = a string of the top card
#   unotable[7]    = an array of member/user objects to send pm's to
    async def cmd_makeuno(self, channel, author):
        '''
        Usage:
            !makeuno
            Literally creates an uno game. Usually doesn't work if a game is already happening.
        '''
        global unotable
        try:
            print(unotable[0][0])
        except:
            unotable = [["."],[".",0,0,0,0,0,0],[],[],[],[],".",[]]
        if unotable[1][1] == 1:
            return Response("Dude you can't make a new uno game when one's already happening in channel "+unotable[0][0], delete_after=5)
        else:
            if unotable[1][3] == True:
                return Response("Dude you can't make another uno game when one's already starting. Say !join in channel "+unotable[0][0], delete_after=20)
            unotable = [[channel.name, channel],[True,False,False,True,0,True,False],[0],[0],[dict()],[author.name],"nothing",[author]]
            unotable[6] = " ".join(convcard(cards(1)[0].split()))
            print(unotable[6])
            unotable[4] = {author.name:cards(7)}
            while unotable[6] in ["w", "wd4", "s", "r", "d2", "Wild", "WildDraw4", "Skip Red", "Skip Green", "Skip Yellow", "Skip Blue", "Reverse Red", "Reverse Blue", "Reverse Green", "Reverse Yellow", "Draw2 Red", "Draw2 Green", "Draw2 Yellow", "Draw2 Blue"]:
                unotable[6] = " ".join(convcard(cards(1)[0].split()))
                print("topcard switched")
            unotable[7] = [author]
            await self.send_message(unotable[0][1], "An Uno game is starting, my dudes :ok_hand: say !join to join, leave by saying !quituno. !startgame starts the game. !botjoingame adds me to the game.")
            if unotable[0][1] != channel.server.default_channel:
                await self.send_message(channel.server.default_channel, "An Uno game is starting, my dudes :ok_hand: get the fuck into "+unotable[0][0]+" and say !join, leave by saying !quituno. !startgame starts the game. !botjoingame adds me to the game.")
            await self.send_message(channel, author.name+" is player number 0.")
    async def cmd_join(self, channel, author):
        '''
        Usage:
            !join
            Join an uno game after creation at any point even after it starts.
        '''
        global unotable
        if unotable[1][3] != True:
            return Response("You can't join a game that doesn't exist, dude", delete_after=5)
        if author.name in unotable[5]:
            return Response("You can't play twice, dude.", delete_after=5)
        unotable[3][0] = unotable[3][0] + 1
        unotable[4][author.name] = cards(7)
        unotable[5].append(author.name)
        unotable[7].append(author)
        await self.send_message(channel, author.name+" is player number "+str(unotable[3][0]))
    async def cmd_startgame(self, channel, author, server):
        '''
        Usage:
            !startgame
            Start an uno game after it is created.
        '''
        global unotable
        if unotable[1][5] != True:
            return Response("You can't start a game that never existed, dude.", delete_after=5)
        if author.name not in unotable[5]:
            return Response("A nonplayer can't start the game, dude.", delete_after=5)
        if unotable[1][1] == True:
            return Response("You can't start a started game, dude.", delete_after=5)
        if unotable[3][0] < 1:
            return Response("You can't start a solo game, dude.", delete_after=5)
        await self.send_message(channel, "It is now "+unotable[5][unotable[2][0]]+"'s turn.")
        await self.send_message(channel, "The top card is: "+" ".join(colorize(unotable[6].split(), server)))
        unotable[1][1] = 1
        for person in unotable[7]:
            tmpstr = ""
            for x in unotable[4][person.name]:
                tmpstr = tmpstr + ", " + " ".join(convcard(x.split()))
            if person.name != self.user.name:
                await self.send_message(person, "Your cards right now: "+tmpstr.strip(","))
    async def cmd_quituno(self, channel, author, server):
        '''
        Usage:
            !quituno
            Leave the current game of uno. If only 1 player remains, the game ends.
        '''
        global unotable
        if unotable[1][5] != True:
            return Response("You can't leave a game that never existed, dude.", delete_after=5)
        if author.name not in unotable[5]:
            return Response("You can't leave a game you aren't in, dude.", delete_after=5)
        remstr = remplayer(author.name)
        if remstr == "LACK OF PLAYERS":
            await self.send_message(channel, "The game must end because there are too few players left...")
            return Response(":joy: :gun:", delete_after=5)
        elif remstr == "MOVETURN":
            await self.send_message(channel, author.nick+" has left and it is now "+unotable[5][unotable[2][0]]+"'s turn.")
            await self.send_message(channel, "The top card is: "+" ".join(colorize(unotable[6].split(), server)))
        else:
            await self.send_message(channel, "Looks like "+author.name+" is out of the game.")
    async def cmd_unokick(self, channel, author, server, user_mentions):
        '''
        Usage:
            !unokick @Username
            Kick someone from an uno game.
        '''
        global unotable
        if unotable[1][5] != True:
            return Response("You can't kick someone from a game that never existed.", delete_after=5)
        if user_mentions[0].name not in unotable[5]:
            return Response("You can't kick someone who isn't in the game.", delete_after=5)
        remstr = remplayer(user_mentions[0].name)
        if remstr == "LACK OF PLAYERS":
            await self.send_message(channel, "The game must end because there are too few players left...")
            return Response(":joy: :gun:", delete_after=5)
        elif remstr == "MOVETURN":
            await self.send_message(channel, user_mentions[0].name+" was kicked and it is now "+unotable[5][unotable[2][0]]+"'s turn.")
            await self.send_message(channel, "Top top card is: "+" ".join(colorize(unotable[6].split(), server)))
        else:
            await self.send_message(channel, "Looks like "+user_mentions[0].name+" got kicked from the game.")
    async def cmd_stopgame(self, channel, author):
        '''
        Usage:
            !stopgame
            Stops an uno game already in progress.
        '''
        global unotable
        if unotable[1][5] != True:
            return Response("You can't stop a game that never existed, dude.", delete_after=5)
        if author.name not in unotable[5]:
            return Response("You can't stop a game you never had anything to do with.", delete_after=5)
        unotable = [["."],[".",0,0,0,0,0,0],[],[],[],[],".",[]]
        await self.send_message(channel, "Uno game stopped.")
    async def cmd_showcards(self, channel, author):
        '''
        Usage:
            !showcards
            Make the bot PM your cards to you again.
        '''
        global unotable
        if author.name not in unotable[5]:
            return Response("You don't have cards.", delete_after=5)
        tmpstr = ""
        for x in unotable[4][author.name]:
            tmpstr = tmpstr + ", " + " ".join(convcard(x.split()))
        await self.send_message(author, "Your cards: "+ tmpstr.strip(","))
    async def cmd_topcard(self, channel, author, server):
        '''
        Usage:
            !topcard
            Check the top card in an uno game already in progress.
        '''
        global unotable
        if unotable[1][5] != True:
            return Response("You can't see the top card of a game that never existed.", delete_after=5)
        await self.send_message(channel, "The top card is: "+" ".join(colorize(unotable[6].split(), server)))
    async def cmd_draw(self, channel, author, server, sendpm=True):
        '''
        Usage:
            !draw
            Draw a single uno card in a game already in progress when it is your turn. Possible up to 5 times even if you can play a card.
        '''
        global unotable
        if unotable[1][5] != True:
            return Response("You can't draw for a game that never existed.", delete_after=5)
        if author.name not in unotable[5]:
            return Response("You can't get cards if you aren't in the game.", delete_after=5)
        if author.name != unotable[5][unotable[2][0]]:
            return Response("You can't draw if it isn't your turn.", delete_after=5)
        if unotable[1][1] != True:
            return Response("The game hasn't started.", delete_after=5)
        if unotable[5][unotable[2][0]] == author.name:
            if unotable[1][4] == 5:
                nextturn()
                await self.send_message(channel, "Force Pass! You did not draw a card. It is now "+unotable[5][unotable[2][0]]+"'s turn.")
                await self.send_message(channel, "The top card is: "+" ".join(colorize(unotable[6].split(), server)))
                tmpstr = ""
                for x in unotable[4][unotable[5][unotable[2][0]]]:
                    tmpstr = tmpstr + ", " + " ".join(convcard(x.split()))
                for person in unotable[7]:
                    if person.name == unotable[5][unotable[2][0]]:
                        await self.send_message(person, "Your cards right now: "+tmpstr.strip(","))
                unotable[1][4] = 0
                return "passed"
            print(unotable[4][author.name])
            newcard = cards(1)[0]
            oldcards = unotable[4][author.name].copy()
            #unotable[4][author.name] = oldcards.append(newcard)
            unotable[4][author.name].append(newcard)
            print(unotable[4][author.name])
            if sendpm==True:
                await self.send_message(author, author.name+", you got a "+" ".join(convcard(newcard.split())))
            unotable[1][2] = True
            unotable[1][4] = unotable[1][4] + 1
            await self.send_message(channel, "Card drawn. You may draw "+str(5-unotable[1][4])+" more cards before being forced to !pass.")
    async def cmd_pass(self, channel, author, server):
        '''
        Usage:
            !pass
            Pass your turn in an uno game already in progress when it is your turn and you have drawn at least one time.
        '''
        global unotable
        if unotable[1][5] != True:
            return Response("You can't pass in a game that never existed.", delete_after=5)
        if author.name not in unotable[5]:
            return Response("You can't pass if you aren't in the game.", delete_after=5)
        if unotable[1][2] == False:
            return Response("You can't pass if you haven't drawn a card.", delete_after=5)
        nextturn()
        await self.send_message(channel, "Pass! It is now "+unotable[5][unotable[2][0]]+"'s turn.")
        await self.send_message(channel, "The top card is: "+" ".join(colorize(unotable[6].split(), server)))
        unotable[1][4] = 0
        tmpstr = ""
        for x in unotable[4][unotable[5][unotable[2][0]]]:
            tmpstr = tmpstr + ", " + " ".join(convcard(x.split()))
        for person in unotable[7]:
            if person.name == unotable[5][unotable[2][0]] and person.name != self.user.name:
                await self.send_message(person, "Your cards right now: "+tmpstr.strip(","))
        unotable[1][2] = False
        if unotable[5][unotable[2][0]] == self.user.name:
            print("Its the bots turn!!")
            botcanplay = False
            topcrdarr = convcard(unotable[6].split())
            for card in unotable[4][self.user.name]:
                cardarr = card.split()
                if len(cardarr) == 1 or cardarr[0] == topcrdarr[0] or cardarr[1] == topcrdarr[1]:
                    botcanplay = True
                    break
            if botcanplay == False:
                await self.send_message(channel, "!draw")
                await self.cmd_draw(channel, self.user, sendpm=False)
                print("I had to draw")
                for card in unotable[4][self.user.name]:
                    cardarr = card.split()
                    if len(cardarr) == 1 or cardarr[0] == topcrdarr[0] or cardarr[1] == topcrdarr[1]:
                        botcanplay = True
                        break
                if botcanplay == True:
                    print("I can play a card.")
                    if len(cardarr) > 1:
                        sntmsg = await self.send_message(channel, "!plcard "+cardarr[0]+" "+cardarr[1])
                    else:
                        wcolr = "r"
                        for x in unotable[4][self.user.name]:
                            if len(x.split()) > 1:
                                wcolr = x.split()[1]
                            if wcolr == "r":
                                wcolr == "b"
                            else:
                                wcolr == "r"
                        sntmsg = await self.send_message(channel, "!plcard "+cardarr[0]+" "+wcolr)
                    await self.cmd_plcard(channel, self.user, sntmsg, sendpm=False)
                else:
                    print("I had to pass")
                    await self.send_message(channel, "!pass")
                    await self.cmd_pass(channel, self.user)
            else:
                print("I can play a card.")
                if len(cardarr) > 1:
                    sntmsg = await self.send_message(channel, "!plcard "+cardarr[0]+" "+cardarr[1])
                else:
                    wcolr = "r"
                    for x in unotable[4][self.user.name]:
                        if len(x.split()) > 1:
                            wcolr = x.split()[1]
                        if wcolr == "r":
                            wcolr == "b"
                        else:
                            wcolr == "r"
                    sntmsg = await self.send_message(channel, "!plcard "+cardarr[0]+" "+wcolr)
                await self.cmd_plcard(channel, self.user, sntmsg, sendpm=False)
            unotable[1][2] = False
            unotable[1][4] = 0
                
    async def cmd_showturn(self, channel, author):
        '''
        Usage:
            !showturn
            Show the player whose turn it currently is in a running game of uno. Shows a list of players in the game.
        '''
        global unotable
        if unotable[1][5] != True:
            return Response("It is nobody's turn in a game that never existed.", delete_after=5)
        if unotable[1][1] != True:
            return Response("It is nobody's turn in a game that hasn't started.", delete_after=5)
        await self.send_message(channel, "It is currently "+unotable[5][unotable[2][0]]+"'s turn.")
        if unotable[2][0] + 1 > unotable[3][0] and unotable[1][0] == True:  #if next turn is too high and normal gameplay  
            nnick = unotable[5][0]                                  #nnick = first guy in unotable[5]
        elif unotable[2][0] - 1 < 0 and unotable[1][0] == False:    #if next turn is too low and reverse gameplay
            nnick = unotable[5][unotable[3][0]]                     #nnick = last guy in unotable[5]
        else:                                       #if any other case
            nnick = unotable[5][unotable[2][0]+1]   #nnick = next guy in unotable[5]
        await self.send_message(channel, "Next turn it will be "+nnick+"'s turn unless a reverse is played.")
        await self.send_message(channel, "The list of players in the game in no particular order: "+", ".join(unotable[5]))
        
    async def cmd_showcount(self, channel, author):
        '''
        Usage:
            !showcount
            Show how many cards everyone in the game has.
        '''
        global unotable
        if unotable[1][5] != True:
            return Response("Nobody has cards if the game doesn't exist.", delete_after=5)
        if unotable[1][1] != True:
            return Response("Everyone has 7 cards, dummy. The game hasn't started", delete_after=5)
        numret = []
        for person in unotable[5]:
            numret.append(person+": "+str(len(unotable[4][person])))
        await self.send_message(channel, ". ".join(numret))
    async def cmd_plcard(self, channel, author, message, server, sendpm=True):
        '''
        Usage:
            !plcard cardvalue color
            Plays a card in a running uno game when it is your turn and it is possible to play the card. Most forms of words or numbers work.
        '''
        global unotable
        
        print(unotable[2][0])
        print(unotable[3][0])
        print(unotable[5])
        print(unotable[4])
        if unotable[1][5] != True:
            return Response("You can't play in a game that never existed.", delete_after=5)
        if unotable[1][1] == 0:
            return Response("The game hasn't started.", delete_after=5)
        if author.name not in unotable[5]:
            return Response("You can't play a card if you aren't in the game.", delete_after=5)
        if author.name != unotable[5][unotable[2][0]]:
            return Response("You can't play a card if it isn't your turn.", delete_after=5)
        allargs = message.content.strip().split()
        allargs.pop(0)  #allargs = [card, color]
        if len(allargs) != 2:
            return Response("You need to !plcard card color", delete_after=5)
        else:
            if iscard(allargs) == False:
                return Response("You need to !plcard card color", delete_after=5)
            if allargs[1].lower() in ["red", "green", "blue", "yellow"] or allargs[0].lower() in ["skip", "wild", "draw2", "reverse", "wilddraw4"]:
                nuarrgs = convcard(allargs) #nu is used for user input and not the top card
                usenu = False
                allargs = nuarrgs.copy()    #this will turn the player input into usable stuff
                nuarrgs = convcard(nuarrgs)
            else:
                nuarrgs = convcard(allargs) #this just gives us a clean version to use later
                usenu = True   #nu is used for the top card
            plyrcard = allargs[0]
            plyrcolr = allargs[1]
            topcrdarr = convcard(unotable[6].split())       #topcrdarr now becomes a dirty version
            topcrd = topcrdarr[0]
            topcolr = topcrdarr[1]
            print(allargs)
            print("allargsvstopcrd")
            print(topcrdarr)
            if plyrcard.lower()+" "+plyrcolr.lower() not in unotable[4][author.name] and plyrcard.lower() not in ["w", "wd4"]:
                return Response("You need to have the card in order to play it", delete_after=5)
            if topcolr.lower() == plyrcolr.lower() or plyrcard.lower() == topcrd.lower() or plyrcard.lower() in ["wd4", "w"]:
                if plyrcard not in ["wd4", "w"]:
                    delcard(' '.join(allargs),author.name)
                else:
                    delcard(plyrcard,author.name)
                if usenu == True:
                    unotable[6] = ' '.join(nuarrgs)
                else:
                    unotable[6] = ' '.join(nuarrgs)
                if plyrcard == "d2":
                    nextturn()
                    unotable[4][unotable[5][unotable[2][0]]].extend(cards(2))
                    lstplyr = unotable[5][unotable[2][0]]
                    lstplyrobj = unotable[7][unotable[2][0]]
                    nextturn()
                    await self.send_message(channel, lstplyr+" got skipped and drew 2 cards.")
                    #for i in range(len(unotable[5])):
                    #    await self.send_message(lstplyrobj, "Your cards right now: "+", ".join(unotable[4][unotable[7][i].name]))
                elif plyrcard == "s":
                    nextturn()
                    lstplyr = unotable[5][unotable[2][0]]
                    nextturn()
                    await self.send_message(channel, lstplyr+" got skipped.")
                elif plyrcard == "r":
                    if unotable[1][0] == True:
                        unotable[1][0] = False
                    else:
                        unotable[1][0] = True
                    nextturn()
                    await self.send_message(channel, author.name+" used a reverse.")
                elif plyrcard == "wd4":
                    if plyrcolr.lower() not in ["y", "g", "r", "b", "red", "blue", "green", "yellow"]:
                        return Response("You need to specify an actual color", delete_after=5)
                    nextturn()
                    #unotable[4][unotable[2][0]].extend(cards(4))
                    unotable[4][unotable[5][unotable[2][0]]].extend(cards(4))
                    lstplyr = unotable[5][unotable[2][0]]
                    nextturn()
                    await self.send_message(channel, lstplyr+" was skipped and drew 4 cards. The color is "+nuarrgs[1])
                    #     for i in range(len(unotable[5])):
                    #         await self.send_message(lstplyr, "Your cards right now: "+", ".join(unotable[4][unotable[7][i].name]))
                elif plyrcard == "w":
                    if plyrcolr.lower() not in ["y", "g", "r", "b", "red", "green", "blue", "yellow"]:
                        return Response("You need to specify an actual color", delete_after=5)
                    nextturn()
                    await self.send_message(channel, author.name+" played a FUCKING WILD CARD! The color is now "+nuarrgs[1])
                else:
                    nextturn()
                    #await self.send_message(channel, plyrcard+" "+plyrcolr+" was played. The top card is now "+unotable[6])
                print(unotable[4][author.name])
                if len(unotable[4][author.name]) == 1:
                    await self.send_message(channel, "OH FUCK! UNO! (on "+author.name+")")
                elif len(unotable[4][author.name]) == 0:
                    await self.send_message(channel, "Congrats to this MOTHERFUCKER for winning: "+author.name)
                    unotable = [["."],[".",0,0,0,0,0,0],[],[],[],[],".",[]]
                    return await self.send_message(channel, "Start another game by saying !makeuno.")
                await self.send_message(channel, author.name+" played. The top card is: "+" ".join(colorize(unotable[6].split(), server)))
                await self.send_message(channel, "It is now "+unotable[5][unotable[2][0]]+"'s turn.")
                if unotable[5][unotable[2][0]] == self.user.name:
                    print("Its the bots turn!!")
                    botcanplay = False
                    topcrdarr = convcard(unotable[6].split())
                    for card in unotable[4][self.user.name]:
                        cardarr = card.split()
                        if len(cardarr) == 1 or cardarr[0] == topcrdarr[0] or cardarr[1] == topcrdarr[1]:
                            botcanplay = True
                            break
                    if botcanplay == False:
                        await self.send_message(channel, "!draw")
                        await self.cmd_draw(channel, self.user, sendpm=False)
                        print("I had to draw")
                        for card in unotable[4][self.user.name]:
                            cardarr = card.split()
                            if len(cardarr) == 1 or cardarr[0] == topcrdarr[0] or cardarr[1] == topcrdarr[1]:
                                botcanplay = True
                                break
                        if botcanplay == True:
                            print("I can play a card.")
                            if len(cardarr) > 1:
                                sntmsg = await self.send_message(channel, "!plcard "+cardarr[0]+" "+cardarr[1])
                            else:
                                wcolr = "r"
                                for x in unotable[4][self.user.name]:
                                    if len(x.split()) > 1:
                                        wcolr = x.split()[1]
                                    if wcolr == "r":
                                        wcolr == "b"
                                    else:
                                        wcolr == "r"
                                sntmsg = await self.send_message(channel, "!plcard "+cardarr[0]+" "+wcolr)
                            await self.cmd_plcard(channel, self.user, sntmsg, sendpm=False)
                        else:
                            print("I had to pass")
                            await self.send_message(channel, "!pass")
                            await self.cmd_pass(channel, self.user)
                    else:
                        print("I can play a card.")
                        if len(cardarr) > 1:
                            sntmsg = await self.send_message(channel, "!plcard "+cardarr[0]+" "+cardarr[1])
                        else:
                            wcolr = "r"
                            for x in unotable[4][self.user.name]:
                                if len(x.split()) > 1:
                                    wcolr = x.split()[1]
                                if wcolr == "r":
                                    wcolr == "b"
                                else:
                                    wcolr == "r"
                            sntmsg = await self.send_message(channel, "!plcard "+cardarr[0]+" "+wcolr)
                        await self.cmd_plcard(channel, self.user, sntmsg, sendpm=False)
                    
                #for i in range(len(unotable[5])):
                #    await self.send_message(unotable[7][i], "Your cards right now: "+", ".join(unotable[4][unotable[7][i].name]))
                #for i in range(len(unotable[5])):
                #    tmpstr = ""
                #    for x in unotable[4][unotable[7][i].name].split():
                #        tmpstr = tmpstr + ", " + " ".join(convcard(x.split()))
                #    await self.send_message(unotable[7][i], "Your cards right now: "+tmpstr)
                tmpstr = ""
                try:
                    if unotable[5][unotable[2][0]] == self.user.name:
                        unotable[1][2] = False
                        unotable[1][4] = 0
                        return ""
                except:
                    print("The game has probably ended and the bot can't figure out whats up. :(")
                    return ""
                if not(sendpm):
                    unotable[1][2] = False
                    unotable[1][4] = 0
                    return ""
                for x in unotable[4][unotable[5][unotable[2][0]]]:
                    tmpstr = tmpstr + ", " + " ".join(convcard(x.split()))
                for person in unotable[7]:
                    if person.name == unotable[5][unotable[2][0]]:
                        await self.send_message(person, "Your cards right now: "+tmpstr.strip(","))
                unotable[1][2] = False
                unotable[1][4] = 0
            else:
                return Response("Either something broke or that card doesn't match the top card", delete_after=5)
    async def cmd_botjoingame(self, author, channel):
        '''
        Usage:
            !botjoingame
            Make the bot join the uno game only once.
        '''
        global unotable
        if unotable[1][3] != True:
            return Response("The bot can't join a game that doesn't exist.", delete_after=5)
        if author.name not in unotable[5]:
            return Response("You can't make the bot join a game you aren't playing.", delete_after=5)
        if unotable[1][6] == True:
            return Response("The bot cannot join the game twice.", delete_after=5)
        unotable[1][6] = True
        unotable[3][0] = unotable[3][0] + 1
        unotable[4][self.user.name] = cards(7)
        unotable[5].append(self.user.name)
        unotable[7].append(self.user)
        await self.send_message(channel, "An AI has joined the game.")
        await self.send_message(channel, self.user.name+" is player number "+str(unotable[3][0]))
    
    async def cmd_getip(self, channel):
        '''
        Returns bot ip
        '''
        try:
            ip = requests.get("https://api.ipify.org").text
            return Response("{}".format(ip), delete_after=10)
        except:
            return Response("Failure.", delete_after=5)
    
    @owner_only
    async def cmd_tester(self, author, message, server, user_mentions, channel):
        '''
        Test command.
        '''
        #print(discord.Member.roles)
        try:
            print(self.activityDict)
            d = datetime.now()
            d2 = datetime.now() - timedelta(days=365)
            print(d2)
            #await self.send_message(channel, "@poco0317")
            #await self.send_message(channel, "@Robotic Overlord")
            #await self.send_message(channel, server.roles[1].mention)
            #print(datetime.now())
            #print(datetime.now()+timedelta(minutes=45))
            #print(datetime.now().hour)
            #link = "http://www.urbandictionary.com/"
            #f = requests.get(link, headers={"content-type":"text"})
            #soup = bS(f.text, "html.parser")
            #found = soup.body.find_all("content", "div", "href", "a", "data-defid")
            #print(soup.body)
            #print(found)
            #found2 = soup.body.find_all("div", {"class":"ribbon"})
            #print("THE FIRST ELEMENT: "+list(found2[0].children)[0].strip())    #POINTER TO DATE
            #found3 = soup.body.find_all("div", {"class":"def-header"})
            #print(found3)
            #print("TEST")
            #print(found3[0])
            #link = "http://dictionary.com/wordoftheday/2017/3/29"
            #f = requests.get(link, headers={"content-type":"text"})
            #soup = bS(f.text, "html.parser")
            #found = soup.body.find_all("li", {"class":"first"})
            #print(found)
            #found = soup.body.find_all("ol", {"class":"definition-list definition-wide-desktop-third definition-desktop-third definition-tablet-third"})
            #print(found)
            #if len(found) == 0:
            #    print("None found")
            #elif found[0] == None:
            #    print("None contents.")
            #for x in found[0].contents:
            #    print(x.string)
            #found = soup.body.find_all("ol", {"class":"definition-list definition-wide-desktop-third definition-desktop-third definition-tablet-first"})
            #print(found[0])
            #print(found[1])
            #print(found[0].string)
            #print(found[0].contents)
            #print(found[0].contents[1].string)
            #for x in found[0].contents:
            #    if len(x.string) > 1:
            #        await self.send_message(channel, x.string)
            #print(found[1].string)
            #print(list(found[0].children)[0])
            #print(list(found3[0].children))
            #print(list(list(found3[0].children)[1].children)[0].strip()) #POINTER TO WORD
            #found4 = soup.body.find_all("div", {"class":"meaning"})
            #found5 = soup.body.find_all("div", {"class":"example"})
            #print(list(found4[0].children)[0].strip()) #pointer to definition
            #print(list(found5[0].children)[0].strip()) #pointer to example usage
            #link = "http://dictionary.com/wordoftheday/"+str(datetime.today().year)+"/"+str(datetime.today().month)+"/"+str(datetime.today().day)+"/"
            #f = requests.get(link, headers={"content-type":"text"})
            #soup = bS(f.text, "html.parser")
            #found = soup.body.find_all("a", "uploaded")
            #link1 = "http://www.urbandictionary.com/"
            #f = requests.get(link1, headers={"content-type":"text"})
            #soup = bS(f.text, "html.parser")
            #found2 = soup.body.find_all("div", {"class":"ribbon"}) #date
            #found3 = soup.body.find_all("div", {"class":"def-header"}) #word
            #found4 = soup.body.find_all("div", {"class":"meaning"}) #definition
            #found5 = soup.body.find_all("div", {"class":"example"}) #example
            #await self.send_message(channel, "Urban Dictionary Word of the Day ("+list(found2[0].children)[0].strip()+"): "+list(list(found3[0].children)[1].children)[0].strip()+"\n**Definition**: "+list(found4[0].children)[0].strip()+"\n**Example**: "+list(found5[0].children)[0].strip())
            #urboutput = "Urban Dictionary Word of the Day ("+list(found2[0].children)[0].strip()+"): "+list(list(found3[0].children)[1].children)[0].strip()+"\n**Definition**: "+list(found4[0].children)[0].strip()+"\n**Example**: "+list(found5[0].children)[0].strip()
            #for x in found:
            #    await self.send_message(channel, "The Dictionary.com Word of the Day is: "+x.contents[1].attrs["alt"]+"\n"+link+"\n\n"+urboutput)
            #for x in found2[0].children:
                #print(x)
            #for x in found2:
                #print(x)
                #print(x.children.children)
                #print("NEXT SERIES")
                #for y in x.contents:
                #    print(y)
            
            #print("test")
            #print(found2)
            #print(soup.get_text())
        except Exception as e:
            print(e)
    
    async def cmd_countinst(self, message, author, channel):
        '''
        Usage:
            !countinst phrase any number of words long
            Checks bar's memory for how many times the phrase occurs.
        '''
        allargs = message.content.strip().split()
        allargs.pop(0)  #allargs = everything but command
        try:
            await self.send_message(channel, str(freqlist.count(" ".join(allargs))))
        except:
            return Response("Error. Nothing was found.", delete_after=5)
    async def cmd_barstats(self, message, author, channel):
        '''
        Displays some fun facts about bar.
        '''
        allargs = message.content.strip().split()
        allargs.pop(0)
        #await self.send_message(channel, "Number of elements in my brain (including repeats): "+str(len(freqlist)))
        #await self.send_message(channel, "Number of elements in my brain (no repeats): "+str(len(freqdict)))
        biggest = 0
        biggestkey = ""
        longest = ""
        for k,v in freqdict.items():
            if int(v) > biggest:
                biggest = int(v)
                biggestkey = k
            if len(k) > len(longest):
                longest = k
        await self.send_message(channel, "Number of elements in my brain (repeats): "+str(len(freqlist))+"\nNumber of elements in my brain (no repeats): "+str(len(freqdict))+"\nMost common element: "+biggestkey+" ("+str(biggest)+" times)\nLongest element: "+longest)
    
    @owner_only
    async def cmd_testhttp(self, author, channel, message):
        '''
        Test command.
        '''
        allargs = message.content.strip().split()
        allargs.pop(0)  #allargs = everything but command
        link = "http://"+allargs[0]
        f = requests.get(link, headers={"content-type":"text"})
        soup = bS(f.text, "html.parser")
        found = soup.body.find_all(allargs[1], allargs[2])
        for x in found:
            print(x.contents)
            print(x.contents[1].attrs["src"], x.contents[1].attrs["alt"])
            pic = re.search("url=(http.+\.png)", re.sub("/{3}", "://", re.sub("%[32][AF]", "/", x.contents[1].attrs["src"]))).group(1)
            await self.send_message(channel, pic)
            await self.send_message(channel, x.contents[1].attrs["alt"])
            for g in x.contents:
                print("1:", g)
                try:
                    print(type(g))
                    print(re.search('(http.+)"', g).group(1))
                    #print(re.search("href=(.+)", x.contents).group(1))
                    #print(re.search("href=(.+)", found).group(1))
                    #print(soup.get_text())
                except Exception as e:
                    print(e)
        #print(f.url)
    async def cmd_searchhttp(self, author, channel, message):
        '''
        !searchhttp http(s)://link key tag tag tag tag ...[infinite tags]
        '''
        allargs = message.content.strip().split()
        allargs.pop(0)
        link = allargs[0]
        if len(allargs) < 3:
            return Response("I need at least 3 parameters.", delete_after=5)
        f = requests.get(link, headers={"content-type":"text"})
        soup = bS(f.text, "html.parser")
        found = soup.body.find_all(allargs[2:])
        for x in found:
            for y in x.contents:
                try:
                    await self.send_message(channel, y.attrs[1])
                except:
                    print("failed somewhere")
    @owner_only
    async def cmd_forcewordoftheday(self, server):
        '''
        Force the bot to tell everyone the word of the day using the daily 6pm trigger. Test command.
        '''
        await self._get_wordofday(server)
    async def cmd_wordoftheday(self, author, channel, message):
        '''
        Force the bot to tell everyone the word of the day.
        '''
        link = "http://dictionary.com/wordoftheday/"+str(datetime.today().year)+"/"+str(datetime.today().month)+"/"+str(datetime.today().day)+"/"
        f = requests.get(link, headers={"content-type":"text"})
        soup = bS(f.text, "html.parser")
        found = soup.body.find_all("a", "uploaded")
        found0 = soup.body.find_all("ol", {"class":"definition-list definition-wide-desktop-third definition-desktop-third definition-tablet-third"})
        if len(found0) == 0:
            found0 = soup.body.find_all("ol", {"class":"definition-list definition-wide-desktop-third definition-desktop-third definition-tablet-first"})
        if len(found0) == 0:
            found0 = soup.body.find_all("ol", {"class":"definition-list definition-wide-desktop-third definition-desktop-first definition-tablet-first"})
        found0Failed = False
        if len(found0) == 0:
            found0Failed = True
        dictdefs = ""
        woop = 1
        if not found0Failed:
            try:
                dictdefs = "    **1**. "
                for x in list(found0[0].contents[1].children)[0].contents:
                    print(x)
                    if x.string and len(x.string) > 1:
                        dictdefs = dictdefs + x.string
                dictdefs = dictdefs + "\n"
                woop = 2
                for x in found0[0].contents:
                    if x.string and len(x.string) > 1:
                        dictdefs = dictdefs + "    **"+str(woop) + "**. " + x.string + "\n"
                        woop = woop+1
            except:
                for x in found0[0].contents:
                    if x.string and len(x.string) > 1:
                        dictdefs = dictdefs + "    **"+str(woop) + "**. " + x.string + "\n"
                        woop = woop+1
                dictdefs = dictdefs + "**Error**: Something went wrong. These definitions may not look right.\n"
        else:
            try:
                causeError = found0[0]
            except Exception as e:
                print(e)
            dictdefs = "**Error**: Something went very wrong when trying to get the definitions. I printed an error related to the issue in the console. Here's a link to the word of the day. "+link
        link1 = "http://www.urbandictionary.com/"
        f = requests.get(link1, headers={"content-type":"text"})
        soup = bS(f.text, "html.parser")
        found2 = soup.body.find_all("div", {"class":"ribbon"}) #date
        found3 = soup.body.find_all("div", {"class":"def-header"}) #word
        found4 = soup.body.find_all("div", {"class":"meaning"}) #definition
        found5 = soup.body.find_all("div", {"class":"example"}) #example
        
        str1 = ""       # definition
        for x in list(found4[0].children):
            #print(type(x))
            #if type(x) == "Tag":
            if x.name == "a":
                #print(list(x.children))
                str1 = str1 + " ".join(list(x.children))
            else:
                #print(x)
                if str(x) != "<br/>":
                    str1 = str1 + " " + str(x)
                else:
                    str1 = str1 + "\n"
        str1 = re.sub("&apos;", "'", str1)
        #print("final:" +str1)
        
        str2 = ""       # example
        #print(list(found5[0].children))
        for x in list(found5[0].children):
            if x.name == "a":
                #print(list(x.children))
                str2 = str2 + " ".join(list(x.children))
            else:
                #print(x)
                if str(x) != "<br/>":
                    str2 = str2 + " " + str(x)
                else:
                    str2 = str2 + "\n"
        str2 = re.sub("&apos;", "'", str2)
        #print("final:" +str2)
                
        #print(list(found2[0].children)[0].strip())
        #print(list(list(found3[0].children)[1].children)[0].strip())
        #print(list(found4[0].children)[0].strip())
        #print(list(found5[0].children)[0].strip())
        
        #print("found3")
        #print(list(found3[0].children))
        #print(len(list(found3[0].children)))
        #print(list(list(found3[0].children)[0].children))
        #urboutput = "UrbanDictionary.com Word of the Day ("+list(found2[0].children)[0].strip()+") is: "+list(list(found3[0].children)[0].children)[0].strip()+"\n**Definition**: "+list(found4[0].children)[0].strip()+"\n**Example**: "+list(found5[0].children)[0].strip()
        #for x in found:
        #        return await self.send_message(channel, "The Dictionary.com Word of the Day is: "+x.contents[1].attrs["alt"]+"\n"+dictdefs+link+"\n\n"+urboutput, embed=None)
        #embed = discord.Embed(colour=discord.Colour(0xc27c0e), description="[Dictionary.com]("+link+") Word of the Day is: **"+found[0].contents[1].attrs["alt"]+"**\n"+dictdefs+"\n[UrbanDictionary]("+link1+") Word of the Day is: **"+list(list(found3[0].children)[0].children)[0].strip()+"**\n**Definition**: "+list(found4[0].children)[0].strip()+"\n**Example**: "+list(found5[0].children)[0].strip())
        embed = discord.Embed(color = discord.Color(0xc27c0e), description="[Dictionary.com]("+link+") Word of the Day is: **"+found[0].contents[1].attrs["alt"]+"**\n"+dictdefs+"\n[UrbanDictionary]("+link1+") Word of the Day is: **"+list(list(found3[0].children)[0].children)[0].strip()+"**\n**Definition**: "+str1+"\n**Example**: "+str2)
        embed.set_author(name="Word of the Day")
        embed.set_footer(text="Produced with no care, I hope it worked", icon_url=self.user.avatar_url)
        return await self.send_message(channel, embed=embed)
    async def cmd_martyr(self, author, channel, message):
        '''
        Increment a joke counter by 1
        '''
        global expired_martyr
        if expired_martyr == 1:
            return Response("Cannot increment more often than every 5 minutes.", delete_after=5)
        expired_martyr = 1
        self.martyrtimer()
        f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/martyrs.txt", "r")
        martyrs = f.read()
        f.close()
        f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/martyrs.txt", "w")
        f.write(str(int(martyrs)+1))
        f.close()
        if author.id == "104388993939951616":
            return await self.send_message(channel, "holy shit :joy: lmaoooo dude you fuckin fell for it "+str(int(martyrs)+1)+" times now :joy: :joy: :joy: :joy: :joy: :joy: :joy: :joy: :joy: :ok_hand:")
        return await self.send_message(channel, "LMAO Soof couldnt be more retarded :joy: he fuckin fell for it "+str(int(martyrs)+1)+" times now :joy: :joy: :joy: :joy: :joy: :joy: :joy: :joy: :joy: :joy: :ok_hand:")
    async def cmd_nukelols(self, author, channel, message):
        '''
        How many times has Nuke said lol since 4/22/17?
        '''
        flol = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/lol.txt", "r")
        lols = flol.read()
        flol.close()
        await self.send_message(channel, "Nuke has said lol "+lols.strip()+" times since 4/22/17.")
    async def cmd_spam(self, author, server):
        '''
        Make the bot pm you 5 times
        '''
        for _ in range(5):
            await self.send_message(author, "you asked for this")
    async def cmd_lmgtfy(self, author, channel, message):
        '''
        Usage:
            !lmgtfy phrase any number of words long
            Spits out a lmgtfy link.
        '''
        msg = message.content.strip().split()
        msg.pop(0)
        await self.send_message(channel, "http://lmgtfy.com/?q="+"+".join(msg))
    def _ytdltest(player, link=""):
        return ""
    @owner_only
    async def cmd_ytdltest(self, server, message, author, channel):
        '''
        Test command.
        '''
        #await self.disconnect_voice_client(server)
        voice = await self.join_voice_channel(self.get_channel("243833327973302274"))
        lank = message.content.strip().split()[1]
        #await self._ytdltest(player, link=lank)
        player = await voice.create_ytdl_player(lank)
        player.start()
        
    async def cmd_clearchan(self, message, channel):
        '''
        Usage:
            !clearchan x
            Clear the last x number of messages, up to 500 and 14 days old.
        '''
        params = message.content.strip().split()
        params.pop(0)
        if len(params) != 1 or int(params[0]) > 500:
            return Response("I need a number of messages to delete. Preferably less than 500...", delete_after=10)
        try:
            await self.purge_from(channel, limit=int(params[0]))
        except:
            return Response("You probably entered a number too high or something went wrong. Messages older than 14 days can't be deleted by me.", delete_after=15)
        await self.send_message(channel, "What messages?")
        
    async def cmd_pushvc(self, message, channel, server):
        '''
        Usage:
            !pushvc up/down[xINTEGER] voicechannel
            Move every member in [voicechannel] up or down 1 channel.
            If given x, (upx5 for example), moves the members that many channels.
        '''
        params = message.content.strip().split()
        params.pop(0)
        if len(params) == 0:
            return Response("You didn't enter parameters.", delete_after=5)
        if len(params) == 1:
            return Response("You didn't finish the parameters.", delete_after=5)
        dir = "nothing"
        params[0] = params[0].split("x")
        if params[0][0] == "up":
            dir = "up"
        if params[0][0] == "down":
            dir = "down"
        pushMult = True
        if len(params[0]) == 1:
            pushMult = False
        pushMultNum = 1
        if pushMult == True:
            try:
                if int(params[0][1]) > 0 and int(params[0][1]) < 50:
                    pushMultNum = int(params[0][1])
                else:
                    return Response("The number you gave was either less than 1 or greater than 50.", delete_after=10)
            except:
                return Response("You tried to multiply up or down by something that wasn't necessarily an integer.", delete_after=10)
        if dir == "nothing":
            return Response("Use up or down.", delete_after=5)
        vctally = -1
        channelto = None
        channelfrom = None
        for channel in server.channels:
            if channel.type == discord.ChannelType.voice:
                vctally = vctally + 1
        for channel in server.channels:
            if channel.type == discord.ChannelType.voice:
                if channel.name.lower() == " ".join(params[1:]).lower():
                    channelfrom = channel
                    channelfromPos = channel.position
                    if dir == "down":
                        channeltoPos = channelfromPos + pushMultNum
                        if channeltoPos > vctally:
                            channeltoPos = channeltoPos%vctally - 1
                    if dir == "up":
                        channeltoPos = channelfromPos - pushMultNum
                        if channeltoPos < 0:
                            while (channeltoPos < 0):
                                channeltoPos = channeltoPos + vctally + 1
        if channelfrom == None:
            return Response("That voice channel does not exist.", delete_after=10)
        for channel in server.channels:
            if channel.type == discord.ChannelType.voice:
                if channel.position == channeltoPos:
                    channelto = channel
        mlist = []
        for member in channelfrom.voice_members:
            mlist.append(member)
        for member in mlist:
            await self.move_member(member, channelto)
        return Response("I have attempted to move everyone in the desired direction, if anyone was there.", delete_after=15)
    async def cmd_funkytown(self, message, channel, server, player):
        '''
        Usage:
            !funkytown #
            Engage funkytown for a number of loops
        '''
        params = message.content.strip().split()
        params.pop(0)
        if player.state == MusicPlayerState.PLAYING:
            return Response("I can't start funkytown because someones playing music :(", delete_after=10)
        if player.ttsrunning == 1:
            return Response("I can't start funkytown because someones using TTS :(", delete_after=10)
        try:
            funkytown = int(float(params[0]))
        except:
            funkytown = 10
        if funkytown > 50:
            return Response("What a waste of time, try something less than 50", delete_after=10)
        vcChans = []
        for channel in server.channels:
            if channel.type == discord.ChannelType.voice:
                vcChans.append(channel)
            if channel.id == "243833327973302274":
                summonchan = channel
        if server.id not in self.players:
            try:
                player = await self.get_player(summonchan, create=True)
                self.players[server.id] = player
            except:
                return Response("Something went wrong :(", delete_after=5)
        player._current_player = player._monkeypatch_player(player.voice_client.create_ffmpeg_player(
            filename="/home/barinade/Desktop/Discordbots/FUNKYTOWN.mp3",
            before_options="-nostdin",
            options="-vn -b:a 128k",
            after=player._playback_finished(forced=True)
        ))
        player._current_player.buff.volume = player.volume
        player.state = MusicPlayerState.STOPPED
        player._current_player.start()
        for _ in range(funkytown):
            await self.move_member(server.me, vcChans[random.randint(0,len(vcChans)-1)])
            time.sleep(2)
        await self.move_member(server.me, summonchan)
        player.stop()
    async def cmd_randvc(self, message, channel, server):
        '''
        Usage:
            !randvc # voicechannel
            Uses a number and a voice channel to send everyone everywhere.
            Similar to pushvc except the place it sends everyone is random...
        '''
        params = message.content.strip().split()
        params.pop(0)
        if len(params) == 0:
            return Response("You didn't enter parameters.", delete_after=5)
        if len(params) == 1:
            return Response("You didn't finish the parameters.", delete_after=5)
        try:
            funkytown = int(float(params[0]))
        except:
            funkytown = 10
        channelfrom = None
        vcChans = []
        for channel in server.channels:
            if channel.type == discord.ChannelType.voice:
                vcChans.append(channel)
                if channel.name.lower() == " ".join(params[1:]).lower():
                    channelfrom = channel
        if channelfrom == None:
            return Response("That voice channel does not exist.", delete_after=10)
        mlist = []
        for member in channelfrom.voice_members:
            mlist.append(member)
        for _ in range(funkytown):
            for member in mlist:
                await self.move_member(member, vcChans[random.randint(0,len(vcChans)-1)])
                time.sleep(0.3)
        for member in mlist:
            await self.move_member(member, channelfrom)
        
    async def cmd_goodtunes(self, message, player, channel, author, server, permissions):
        '''
        Usage:
            !goodtunes [#] [-N, -A, -NA]
            Creates a playlist from the Good Tunes channel, randomly by default.
            If a number is given, it picks that number of songs unless it runs out of songs to choose from.
            If no number is given, it picks 5 songs.
            If a number larger than the list of songs in the channel is given, it will stop when it runs out of links.
            If -N is given, it picks the last 5 or last # songs, turning random off.
            If -A is given, it picks the entire list of song links found.
            If -NA or -AN is given, it picks the entire list of song links found in order.
            The songs must download first to play; this command works exactly like 1play in that respect.
        '''
        if player.tts == 1:
            return Response("TTS is playing. You cannot queue music when TTS is playing.", delete_after=5)
        if not author.voice_channel:
            return Response("You have to be in a voice channel to queue music.", delete_after=10)
        for cnl in server.channels:
            for m in cnl.voice_members:
                if m.id == author.id:
                    if cnl.id != player.voice_client.channel.id:
                        return Response("You must be in the same voice channel as the bot to queue music.", delete_after=10)
        Mainmessage = await self.send_message(channel, "I'll be using this message to confirm when the playlist is done being made... You may stop it early by using !stopgt.\nFirst, I'm creating a list of songs.")
        linklist = []
        for chanel in server.channels:
            if chanel.id == "280862307956031488":
                goodtunes = chanel
        async for msg in self.logs_from(goodtunes, limit=1000):
            link = re.search("(http[s]?://yout[^\s]+)", msg.content)
            link2 = re.search("(http[s]?://www.yout[^\s]+)", msg.content)
            if link:
                linklist.append([link.group(0), msg.author])
            if link2:
                linklist.append([link2.group(0), msg.author])        
        params = message.content.strip().split()
        params.pop(0)
        try:
            numberOfSongs = int(float(params[0]))
        except:
            numberOfSongs = 5
        if numberOfSongs < 1:
            numberOfSongs = 5
        NOTRANDOM = False
        try:
            if params[0] == "-N":
                NOTRANDOM = True
            elif params[1] == "-N":
                NOTRANDOM = True
        except:
            NOTRANDOM = False
        try:
            if params[0] == "-A":
                numberOfSongs = len(linklist)
            elif params[1] == "-A":
                numberOfSongs = len(linklist)
        except:
            numberOfSongs = numberOfSongs
        try:
            if params[0] == "-NA" or params[0] == "-AN":
                numberOfSongs = len(linklist)
                NOTRANDOM = True
            elif params[1] == "-NA" or params[1] == "-AN":
                numberOfSongs = len(linklist)
                NOTRANDOM = True
        except:
            numberOfSongs = numberOfSongs
        Mainmessage = await self.edit_message(Mainmessage, Mainmessage.content+"\nSecond, I'm picking "+str(numberOfSongs)+" songs with random '"+str(not NOTRANDOM)+".'")
        songlist = []
        for i in range(numberOfSongs):
            if NOTRANDOM:
                songlist.append(linklist[i])
            else:
                try:
                    tmpChoice = random.choice(linklist)
                    songlist.append(tmpChoice)
                    linklist.pop(linklist.index(tmpChoice))
                except:
                    break
        Mainmessage = await self.edit_message(Mainmessage, Mainmessage.content+"\nThird, I'm constructing the playlist by running ^play in the background. Your music will probably start before this finishes.")
        #for song in songlist:
        #    await self.cmd_play(player, channel, author, server, permissions, None, song[0], Forced=True, mesag=Mainmessage, ForcedAuthor=song[1])
        #await self.edit_message(Mainmessage, "I'll be using this message to confirm when the playlist is done being made...\nFirst, I'm creating a list of songs.\nSecond, I'm picking "+str(numberOfSongs)+" songs with random '"+str(not NOTRANDOM)+".'\nThird, I'm constructing the playlist by running ^play in the background. Your music will probably start before this finishes.\nDone! Check the ^queue!")
        await self._gt_queuer(Mainmessage, songlist, player=player, channel=channel, author=author, server=server, permissions=permissions)
        
    async def _gt_queuer(self, mainmessage, songlist, player=None, channel=None, author=None, server=None, permissions=None):
        if self.stop_GTQ:
            self.stop_GTQ = False
            return await self.edit_message(mainmessage, mainmessage.content+"\nForcibly stopped!")
        try:
            song = songlist.pop(0)
        except:
            self.stop_GTQ = False
            return await self.edit_message(mainmessage, mainmessage.content+"\nDone! Check the queue if your music isn't playing!")
        await self.cmd_play(player, channel, author, server, permissions, None, song[0], Forced=True, mesag=mainmessage, ForcedAuthor=song[1])
        await self._gt_queuer(mainmessage, songlist, player=player, channel=channel, author=author, server=server, permissions=permissions)
        
    async def cmd_stopgt(self, message, channel, author):
        '''
        Usage:
            !stopgt
            This can be used by anyone to immediately stop the queuing of a list of songs from the Good Tunes channel.
            Useful when you use the -A command with it, because it takes a pretty long time to finish queuing those songs.
        '''
        if not self.stop_GTQ:
            self.stop_GTQ = True
            return Response("I stopped it. The playlist should be stable again.", delete_after=15)
        else:
            return Response("I can't stop what has not been started.", delete_after=10)
            
    async def on_member_join(self, member):
        server = member.server
        #await self.replace_roles(member, server.roles[3])
        await self.send_message(server.default_channel, "oh SHIT guys its a new member: "+member.name+" (check your private messages unless you're a bot)")
        self.newmemberlist.append(member.id)
        await self.send_message(member, "hey fam welcome to Ghost Divison :joy: \nThis server contains some 18+ content, but it's barred from new users via the Regular+ role. Ask an admin for it.\nPLEASE NOTE: you are not allowed to do anything on this server until you reply to this message (say anything you want, only I can see it)")
        fl = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/idlist.txt", "a")
        fl.write("\n"+member.id)
        fl.close()
        f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/removed.txt", "a")
        curtime = [str(datetime.today().year), str(datetime.today().month), str(datetime.today().day), str(datetime.today().hour), str(datetime.today().minute)]
        #if int(curtime[3]) > 12:
        #    curtime[3] = str(int(curtime[3])-12)
        try:
            f.write("\nJoined: "+member.name+" ("+member.id+") at "+curtime[1]+" "+curtime[2]+" "+curtime[0]+" "+":".join(curtime[3:]))
        except:
            f.write("\nJoined: "+member.id+" at "+curtime[1]+" "+curtime[2]+" "+curtime[0]+" "+":".join(curtime[3:]))
        f.close()
    async def on_member_ban(self, member):
        f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/removed.txt", "a")
        curtime = [str(datetime.today().year), str(datetime.today().month), str(datetime.today().day), str(datetime.today().hour), str(datetime.today().minute)]
        #if int(curtime[3]) > 12:
        #    curtime[3] = str(int(curtime[3])-12)
        try:
            f.write("\nBANNED: "+member.name+" ("+member.id+") at "+curtime[1]+" "+curtime[2]+" "+curtime[0]+" "+":".join(curtime[3:]))
        except:
            f.write("\nBANNED: "+member.id+" at "+curtime[1]+" "+curtime[2]+" "+curtime[0]+" "+":".join(curtime[3:]))
        await self.send_message(self.modchan, "BANNED: "+member.name)
        await self.send_message(self.alertchan, "BANNED: "+member.name)
        f.close()
    async def on_member_remove(self, member):
        f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/removed.txt", "a")
        curtime = [str(datetime.today().year), str(datetime.today().month), str(datetime.today().day), str(datetime.today().hour), str(datetime.today().minute)]
        #if int(curtime[3]) > 12:
        #    curtime[3] = str(int(curtime[3])-12)
        try:
            f.write("\nREMOVED or LEFT: "+member.name+" ("+member.id+") at "+curtime[1]+" "+curtime[2]+" "+curtime[0]+" "+":".join(curtime[3:]))
        except:
            f.write("\nREMOVED or LEFT: "+member.id+" at "+curtime[1]+" "+curtime[2]+" "+curtime[0]+" "+":".join(curtime[3:]))            
        await self.send_message(self.modchan, "("+self.adminrole.mention+") LEFT/KICKED: "+member.name)
        await self.send_message(self.alertchan, "("+self.adminrole.mention+") LEFT/KICKED: "+member.name)
        f.close()
    async def on_member_update(self, before, after):
        #status-activity is made of dicts of UIDs:vars
        if before.status != after.status:
            d = datetime.now()
            if before.id not in self.activityDict:
                self.activityDict[before.id] = [str(after.status), '{:%m/%d/%Y %H:%M:%S}'.format(d)]
                f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/activity.txt", "a")
                f.write(before.id+"@"+"@".join(self.activityDict[before.id]).strip())
                f.close()
            else:
                f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/activity.txt", "w")
                self.activityDict[before.id] = [str(after.status), '{:%m/%d/%Y %H:%M:%S}'.format(d)]
                f.write("Line@Number@One")
                for k,v in self.activityDict.items():
                    if k != "Line":
                        f.write("\n"+k+"@"+"@".join(v).strip())
                f.close()
    
    
    
    
    
    
    
        elif before.nick != after.nick: #nick difference found
            if before.nick == None:
                await self.send_message(self.modchan, 'User '+before.name+' set their nickname to "'+after.nick+'"')
                await self.send_message(self.alertchan, 'NICKNAME CHANGE: '+before.name+' set their nickname to "'+after.nick+'"')
            elif after.nick == None:
                await self.send_message(self.modchan, 'User '+before.name+' had their nickname removed.')
                await self.send_message(self.alertchan, 'NICKNAME CHANGE: '+before.name+' had their nickname removed.')
            else:
                await self.safe_send_message(self.modchan, 'User '+before.name+' had their nickname changed from "'+before.nick+'" to "'+after.nick+'"')
                await self.safe_send_message(self.alertchan, 'NICKNAME CHANGE: '+before.name+' had their nickname changed from "'+before.nick+'" to "'+after.nick+'"')
            
        if before.roles != after.roles: #role difference found
            blist = ""
            for br1 in before.roles:
                if br1.name == "@everyone":
                    blist = blist+", `"+br1.name+"`"
                else:
                    blist = blist+", "+br1.name
            alist = ""
            for ar1 in after.roles:
                if ar1.name == "@everyone":
                    alist = alist+", `"+ar1.name+"`"
                else:
                    alist = alist+", "+ar1.name
            await self.safe_send_message(self.modchan, "Role change on user: "+before.name+"\nRoles Before: "+blist+"\nRoles After: "+alist)
            
            
    def barstfutimer(self,tinsecond=300):
        global barquiet
        #tinsecond = 300
        global timerun
        timerun = Timer(tinsecond, self.resetbarquiet)
        timerun.start()
    def resetbarquiet(self):
        global barquiet
        barquiet = 0
        print("timer expired")
    def barusetimer(self, tinsecond=15):
        global baruse   #1/go == allowed
        global timerun_baruse
        timerun_baruse = Timer(tinsecond, self.resetbaruse)
        timerun_baruse.start()
    def resetbaruse(self):
        global baruse
        baruse = "go"
        print("timer expired")
    def msgcooldowntimer(self,tinsecond=5):
        global timerun_msgcd
        global expired_cdt
        timerun_msgcd = Timer(tinsecond, self.resetmsgcdt)
        timerun_msgcd.start()
    def resetmsgcdt(self):
        global expired_cdt
        expired_cdt = 0
        print("cdt expired")
    def martyrtimer(self,tinsecond=360):
        timerun_martyr = Timer(tinsecond, self.resetmartyr)
        timerun_martyr.start()
    def resetmartyr(self):
        global expired_martyr
        expired_martyr = 0
        print("cdt expired")
    def ttstimekeeper(self,tinsecond=5):
        global ttstimer
        ttstimer = 1
        timerun_tts = Timer(tinsecond, self.resetttstimer)
        timerun_tts.start()
    def resetttstimer(self):
        global ttstimer
        ttstimer = 0
    def barmemorysavetimer(self,tinsecond=1):
        global barsaver #1 == "timer running"
        barsaver = 1
        global timerun_barsaver
        timerun_barsaver = Timer(tinsecond, self.resetbarsaver)
        timerun_barsaver.start()
    def resetbarsaver(self):
        f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/wordfreq.txt", "w")
        global freqdict
        for k,v in freqdict.items():
            f.write(k+","+str(v)+"\n")
        f.close()
        print("bar memory saved - loop done")
        #timerun_barsaver = Timer(600, self.resetbarsaver)
        #timerun_barsaver.start()
    @owner_only
    async def cmd_barpurge(self, message, author, channel):
        '''
        Usage:
            !barpurge [purgeallitems] phrase any number of words long
            Purge the phrase from bar's memory. Purgeallitems flag cleanses the entire memory.
        '''
        global freqlist
        global freqdict
        phrase = message.content.split()
        phrase.pop(0)
        if phrase[0] == "purgeallitems":
            freqlist = []
            freqdict = {"michael":1,"jordan":1}
            return Response("Mission accomplished.", delete_after=5)
        phrase = " ".join(phrase)
        print("phrase:", phrase)
        try:
            del freqdict[phrase]
            freqlist = []
            for k,v in freqdict.items():
                for _ in range(int(v)):
                    freqlist.append(k)
            return Response("Gone", delete_after=5)
        except Exception as e:
            print(e)
            return Response("Failure.", delete_after=5)
            
    async def cmd_bartts(self, player, message, author, channel, server):
        '''
        Usage:
            !bartts [anything here]
            Triggers a response from bar except in tts form.
        '''
        if not author.voice_channel:
            return Response("You have to be in a voice channel to hear TTS.", delete_after=10)
        player.voice_client
        for cnl in server.channels:
            for m in cnl.voice_members:
                if m.id == author.id:
                    if cnl.id != player.voice_client.channel.id:
                        return Response("You must be in the same voice channel as the bot to hear TTS.", delete_after=10)
        if player.state == MusicPlayerState.PLAYING:
            return Response("Music is playing. You cannot use TTS right now.", delete_after=10)
        global freqdict
        msgwords = re.sub("[^a-zA-Z0-9\,\.\? <>:@\!\#\&]+", "", message.content).split()
        print(msgwords)
        msgwords.pop(0)
        if len(msgwords) == 0:
            msgwords.append("the")
        tmpmsgwrds = msgwords.copy()
        for i in range(len(msgwords)):
            if tmpmsgwrds[i].startswith("http") or tmpmsgwrds[i].startswith("www."):
                msgwords.remove(tmpmsgwrds[i])
        wordsphrase = list()
        nxtwrphr = ""
        if len(msgwords) > 2:
            for w in msgwords:
                if random.randint(1,10) > 3:
                    if nxtwrphr == "":
                        nxtwrphr = w
                    else:
                        nxtwrphr = nxtwrphr + " " + w
                else:
                    if nxtwrphr == "":
                        wordsphrase.append(w)
                    else:
                        wordsphrase.append(nxtwrphr)
                        nxtwrphr = w
            if nxtwrphr != "":
                wordsphrase.append(nxtwrphr)
                nxtwrphr = ""
        else:
            wordsphrase = msgwords.copy()
        for w in wordsphrase:
            if w in freqdict:
                freqdict[w] = str(int(freqdict[w]) + 1)
            else:
                freqdict[w] = "1"
            freqlist.append(w)
        nxtmsg = list()
        incmsg = ""
        verbs = ["is", "should", "be", "should be", "isn't", "may be", "can", "may", "could be", "would be", "has", "gets", "is"]
        namelist = ["tox", "poco", "soof", "arteth", "arty", "cody", "mar", "mario", "john", "tails", "guner", "vexx", "redd", "ukrainian", "atanga", "signis", "lazarus", "nansae", "ronwe", "emeris", "relay", "rythoka", "bae", "baewulf", "miri", "demo", "mpra2"]
        if msgwords[0].lower() in namelist and len(msgwords) == 1:
            sndmsg = msgwords[0]
            sndmsg = sndmsg+" "+verbs[random.randint(0,len(verbs)-1)]
            for _ in range(random.randint(1,10)):
                sndmsg = sndmsg+" "+freqlist[random.randint(0,len(freqlist)-1)]
            print("1")
            player.ttsqueue.append(sndmsg)
            player.tts = 1
            player.volume = 2
            player.ttstime = 1
            await self.send_message(channel, sndmsg)
            return await self._tts_controller(player)
            #return await self.send_message(channel, sndmsg) #####################activate tts here
        if msgwords[0].lower() in namelist and len(msgwords) > 1:
            sndmsg = msgwords[0]
            if msgwords[1] in verbs:
                sndmsg = sndmsg+" "+msgwords[1]
            added = 0
            for _ in range(random.randint(1,10)):
                sndmsg = sndmsg+" "+freqlist[random.randint(0,len(freqlist)-1)]
                if random.randint(1,10) > 3 and added == 0 and msgwords[1] in verbs:
                    sndmsg = sndmsg+" "+" ".join(msgwords[2:])
                    added = 1
                elif random.randint(1,10) > 3 and added == 0 and msgwords[1] not in verbs:
                    sndmsg = sndmsg+" "+" ".join(msgwords[1:])
                    added = 1
            print("2")
            player.ttsqueue.append(sndmsg)
            player.tts = 1
            player.volume = 2
            player.ttstime = 1
            await self.send_message(channel, sndmsg)
            return await self._tts_controller(player)
            #return await self.send_message(channel, sndmsg) ##############activate tts here
        for _ in range(random.randint(1,random.randint(3,13))):
            nxtmsg.append(freqlist[random.randint(0,len(freqlist)-1)])
        nwmsg = 1
        for x in nxtmsg:
            if random.randint(1,10) > 3 and nwmsg == 1 and len(wordsphrase) > 1:
                incmsg = incmsg + " " + wordsphrase[random.randint(0,len(wordsphrase)-1)]
                nwmsg = 0
            if x in punctmrks:
                incmsg = incmsg+x
            else:
                incmsg = incmsg+" "+x
        nuincmsg = incmsg.strip().split()
        for i in range(len(nuincmsg)):
            try:
                if (nuincmsg[i].endswith(".") or nuincmsg[i].endswith("?") or nuincmsg[i].endswith("!")) and len(nuincmsg) > 2:
                    nuincmsg.append(nuincmsg[i])
                    nuincmsg.pop(len(nuincmsg)-2)
                    nuincmsg.remove(nuincmsg[i])
                if nuincmsg[i].endswith(",") and i == len(nuincmsg)-1:
                    nuincmsg[i] = re.sub("$,", "", nuincmsg[i])
            except:
                print("ran out of index range")
        sndmsg = ""
        for x in nuincmsg:
            sndmsg = sndmsg+" "+x
        print("3")
        player.ttsqueue.append(sndmsg)
        player.tts = 1
        player.volume = 2
        player.ttstime = 1
        await self.send_message(channel, sndmsg)
        await self._tts_controller(player)
        #await self.send_message(channel, sndmsg) ##############activate tts here
            
            
    async def cmd_tts(self, player, message, author, channel, server):
        '''
        Usage:
            !tts words
            Uses DECtalk TTS in the voice channel the bot is in.
        '''
        #check here if ttsrunning is 1 (then queue if it is)
        await self.delete_message(message)
        if len(message.content.strip().split())<2:
            return Response("Command usage: !tts blah blah blah", delete_after=5)
        if not author.voice_channel:
            return Response("You have to be in a voice channel to hear TTS.", delete_after=10)
        player.voice_client
        for cnl in server.channels:
            for m in cnl.voice_members:
                if m.id == author.id:
                    if cnl.id != player.voice_client.channel.id:
                        return Response("You must be in the same voice channel as the bot to hear TTS.", delete_after=10)
        if player.state == MusicPlayerState.PLAYING:
            return Response("Music is playing. You cannot use TTS right now.", delete_after=10)
        if player.ttsrunning == 1:
            player.ttsqueue.append(" ".join(message.content.strip().split()[1:]))
            return Response(" TTS queued (it will autoplay).", reply=True, delete_after=3)
        player.tts = 1
        player.volume = 2
        if re.search("\[:t", " ".join(message.content.strip().split()[1:])) or re.search("\[:dv", " ".join(message.content.strip().split()[1:])) or re.search("\[:dial", " ".join(message.content.strip().split()[1:])):
            player.volume = 0.4
        os.system('cd "/home/barinade/.wine/drive_c/Program Files (x86)/DECtalk/Us/"')
        os.system('sudo --user=barinade wine say.exe -w /home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav [:phoneme on] '+'"'+" ".join(message.content.strip().split()[1:])+'"')
        player._current_player = player._monkeypatch_player(player.voice_client.create_ffmpeg_player(
            filename="/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav",
            before_options="-nostdin",
            options="-vn -b:a 128k",
            after=player._playback_finished(forced=True)
        ))
        player._current_player.buff.volume = player.volume
        player.state = MusicPlayerState.STOPPED
        process = subprocess.Popen(['ffmpeg', '-i', '/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav'], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        stdout, stderr = process.communicate()
        matches = re.search(r"Duration:\s{1}(?P<hours>\d+?):(?P<minutes>\d+?):(?P<seconds>\d+\.\d+?),", stdout.decode('utf-8'), re.DOTALL).groupdict()
        matches['hours'] = float(matches['hours'])*60*60
        matches['minutes'] = float(matches['minutes'])*60
        lengthoftime = float(matches['hours'])+float(matches['minutes'])+float(matches['seconds'])
        player.ttstime = int(lengthoftime)
        player._current_player.start()
        print(player)
        await self._tts_controller(player)
    async def _tts_no_cmd(self, player, tts):
        os.system('cd "/home/barinade/.wine/drive_c/Program Files (x86)/DECtalk/Us/"')
        os.system('sudo --user=barinade wine say.exe -w /home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav [:phoneme on] '+'"'+tts+'"')
        player._current_player = player._monkeypatch_player(player.voice_client.create_ffmpeg_player(
            filename="/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav",
            before_options="-nostdin",
            options="-vn -b:a 128k",
            after=player._playback_finished(forced=True)
        ))
        player._current_player.buff.volume = player.volume
        player.state = MusicPlayerState.STOPPED
        process = subprocess.Popen(['ffmpeg', '-i', '/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav'], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        stdout, stderr = process.communicate()
        matches = re.search(r"Duration:\s{1}(?P<hours>\d+?):(?P<minutes>\d+?):(?P<seconds>\d+\.\d+?),", stdout.decode('utf-8'), re.DOTALL).groupdict()
        matches['hours'] = float(matches['hours'])*60*60
        matches['minutes'] = float(matches['minutes'])*60
        lengthoftime = float(matches['hours'])+float(matches['minutes'])+float(matches['seconds'])
        player.ttstime = int(lengthoftime)
        player._current_player.start()
        print(player)
        await self._tts_controller(player)
    async def _tts_controller(self, player):
        #sets flag
        #holds timer
        #checks queue after timer
        player.ttsrunning = 1
        await asyncio.wait_for(asyncio.sleep(player.ttstime), timeout=player.ttstime+5, loop=self.loop)
        if len(player.ttsqueue) > 0:
            await self._tts_no_cmd(player, player.ttsqueue.pop(0))
        player.ttsrunning = 0
        player.tts = 0
        player._current_player = None
        player._current_entry = None
        player.volume = 0.3
    # async def cmd_tts(self, player, message, author, channel):
        # global ttstimer
        # global nxtttsQ
        # global nxtttsQuse
        # msg = message.content.strip().split()
        # msg.pop(0)
        # if len(msg) < 1:
            # return Response("No input locks the bot.", delete_after=5)
        # if player.state == MusicPlayerState.PLAYING:
            # return Response("Music is playing, that's pretty rude to override music with tts.", delete_after=10)
        # nxtttsQ.append(" ".join(msg))
        # if ttstimer == 1:
            # nxtttsQuse = 1
            # return Response("TTS in use. Your tts will be played after the current tts ends and tts is used again.", delete_after=5)
        # player.tts = 1
        # player.playlist.clear()
        # player.volume = 2
        # if re.search("\[:t", " ".join(msg)):
            # player.volume = 0.4
        # if nxtttsQuse == 1:
            # nxtttsQuse = 0
            # os.system('cd "/home/barinade/.wine/drive_c/Program Files (x86)/DECtalk/Us/"')
            # os.system('sudo --user=barinade wine say.exe -w /home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav [:phoneme on] '+'"'+" ".join(nxtttsQ)+'"')
            # process = subprocess.Popen(['ffmpeg', '-i', '/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav'], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            # stdout, stderr = process.communicate()
            # matches = re.search(r"Duration:\s{1}(?P<hours>\d+?):(?P<minutes>\d+?):(?P<seconds>\d+\.\d+?),", stdout.decode('utf-8'), re.DOTALL).groupdict()
            # matches['hours'] = float(matches['hours'])*60*60
            # matches['minutes'] = float(matches['minutes'])*60
            # lengthoftime = float(matches['hours'])+float(matches['minutes'])+float(matches['seconds'])
            # self.ttstimekeeper(tinsecond=lengthoftime)
            # nxtttsQ = []
            # await self.delete_message(message)
        # else:
            # os.system('cd "/home/barinade/.wine/drive_c/Program Files (x86)/DECtalk/Us/"')
            # os.system('sudo --user=barinade wine say.exe -w /home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav [:phoneme on] '+'"'+" ".join(msg)+'"')
            # process = subprocess.Popen(['ffmpeg', '-i', '/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav'], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            # stdout, stderr = process.communicate()
            # matches = re.search(r"Duration:\s{1}(?P<hours>\d+?):(?P<minutes>\d+?):(?P<seconds>\d+\.\d+?),", stdout.decode('utf-8'), re.DOTALL).groupdict()
            # matches['hours'] = float(matches['hours'])*60*60
            # matches['minutes'] = float(matches['minutes'])*60
            # lengthoftime = float(matches['hours'])+float(matches['minutes'])+float(matches['seconds'])
            # self.ttstimekeeper(tinsecond=lengthoftime)
            # nxtttsQ = []
            # await self.delete_message(message)
        # try:
            # await player.pray(_continue=False, filename="/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav")
        # except:
            # print("ignoring errors")
            # #exit(1)
    # @owner_only
    # async def cmd_ttsalt(self, player, message, author, channel):
        # global ttstimer
        # msg = message.content.strip().split()
        # msg.pop(0)
        # if len(msg) < 1:
            # return Response("No input locks the bot.", delete_after=5)
        # if ttstimer == 1:
            # return Response("TTS in use.", delete_after=1)
        # if player.state == MusicPlayerState.PLAYING:
            # return Response("Music is playing, that's pretty rude to override music with tts.", delete_after=10)
        # player.tts = 1
        # player.playlist.clear()
        # player.volume = 2
        # if re.search("\[:t", " ".join(msg)) or re.search("\[:dv", " ".join(msg)) or re.search("\[:dial", " ".join(msg)):
            # player.volume = 0.3
        # os.system('cd "C:\\Program Files (x86)\\DECtalk\\'+msg[0]+'\\"')
        # os.system('sudo --user=barinade wine say.exe -w /home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav [:phoneme on] '+'"'+" ".join(msg[1:])+'"')
        # process = subprocess.Popen(['ffmpeg', '-i', '/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav'], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        # stdout, stderr = process.communicate()
        # matches = re.search(r"Duration:\s{1}(?P<hours>\d+?):(?P<minutes>\d+?):(?P<seconds>\d+\.\d+?),", stdout.decode('utf-8'), re.DOTALL).groupdict()
        # matches['hours'] = float(matches['hours'])*60*60
        # matches['minutes'] = float(matches['minutes'])*60
        # lengthoftime = float(matches['hours'])+float(matches['minutes'])+float(matches['seconds'])
        # self.ttstimekeeper(tinsecond=lengthoftime)
        # await self.delete_message(message)
        # try:
            # await player.pray(_continue=False, filename="/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/test.wav")
        # except:
            # print("ignoring errors")
            
            
            
    def _checkinvitelistloop(self, srvr):
        self.loop.create_task(self._get_invitelist(srvr))
        self.loop.call_later(15, self._checkinvitelistloop, srvr)
    async def _get_invitelist(self, srvr):
        chk = await self.invites_from(srvr)
        chknum = len(chk)
        if chknum > len(self.invitelists[srvr.name]):
            #check to see what the difference is, show what it is in the mod channel
            latest = datetime(1970,1,1)
            for inv in self.invitelists[srvr.name]:
                if inv.created_at > latest:
                    latest = inv.created_at
                    latestOLDinv = inv
            for inv in chk:
                if inv.created_at > latest:
                    latest = inv.created_at
                    latestNEWinv = inv
            for x in srvr.channels:
                if x.id == "264837364415725568":
                    modchannel = x
            await self.send_message(modchannel, "A new invite was created recently by "+latestNEWinv.inviter.name+" and will expire in "+str(latestNEWinv.max_age)+" seconds. (0 means infinite)")
            await self.send_message(self.alertchan, "NEW INVITE: by "+latestNEWinv.inviter.name+" will expire in "+str(latestNEWinv.max_age)+" seconds. (0 means infinite)")
            self.invitelists[srvr.name] = await self.invites_from(srvr)
        elif chknum < len(self.invitelists[srvr.name]):
            print("ALERT: Someone deleted an invite. Reconstructing the invite list.")
            await self.send_message(self.alertchan, "DELETED INVITE: An invite has been deleted either manually or by time expiration.")
            self.invitelists[srvr.name] = await self.invites_from(srvr)
        
    def _wordofthedayloop(self, curtime, srvr):
        #print(curtime)
        #print("vs " + str(time.localtime().tm_hour))
        if time.localtime().tm_hour == 18:
            self.loop.create_task(self._get_wordofday(srvr))
            self.loop.call_later(4000, self._wordofthedayloop, self.loop.time(), srvr)
            return ""
        self.loop.call_later(30, self._wordofthedayloop, self.loop.time(), srvr)
    async def _get_wordofday(self, srvr):
        print("WORD OF THE DAY TRIGGERED (6PM)")
        try:
            link = "http://dictionary.com/wordoftheday/"+str(datetime.today().year)+"/"+str(datetime.today().month)+"/"+str(datetime.today().day)+"/"
            f = requests.get(link, headers={"content-type":"text"})
            soup = bS(f.text, "html.parser")
            found = soup.body.find_all("a", "uploaded")
            found0 = soup.body.find_all("ol", {"class":"definition-list definition-wide-desktop-third definition-desktop-third definition-tablet-third"})
            if len(found0) == 0:
                found0 = soup.body.find_all("ol", {"class":"definition-list definition-wide-desktop-third definition-desktop-third definition-tablet-first"})
            if len(found0) == 0:
                found0 = soup.body.find_all("ol", {"class":"definition-list definition-wide-desktop-third definition-desktop-first definition-tablet-first"})
            found0Failed = False
            if len(found0) == 0:
                found0Failed = True
            dictdefs = ""
            woop = 1
            if not found0Failed:
                try:
                    dictdefs = "    **1**. "
                    for x in list(found0[0].contents[1].children)[0].contents:
                        print(x)
                        if x.string and len(x.string) > 1:
                            dictdefs = dictdefs + x.string
                    dictdefs = dictdefs + "\n"
                    woop = 2
                    for x in found0[0].contents:
                        if x.string and len(x.string) > 1:
                            dictdefs = dictdefs + "    **"+str(woop) + "**. " + x.string + "\n"
                            woop = woop+1
                except:
                    for x in found0[0].contents:
                        if x.string and len(x.string) > 1:
                            dictdefs = dictdefs + "    **"+str(woop) + "**. " + x.string + "\n"
                            woop = woop+1
                    dictdefs = dictdefs + "**Error**: Something went wrong. These definitions may not look right.\n"
            else:
                try:
                    causeError = found0[0]
                except Exception as e:
                    print(e)
                dictdefs = "**Error**: Something went very wrong when trying to get the definitions. I printed an error related to the issue in the console. Here's a link to the word of the day. "+link
            link1 = "http://www.urbandictionary.com/"
            f = requests.get(link1, headers={"content-type":"text"})
            soup = bS(f.text, "html.parser")
            found2 = soup.body.find_all("div", {"class":"ribbon"}) #date
            found3 = soup.body.find_all("div", {"class":"def-header"}) #word
            found4 = soup.body.find_all("div", {"class":"meaning"}) #definition
            found5 = soup.body.find_all("div", {"class":"example"}) #example
            
            str1 = ""       # definition
            for x in list(found4[0].children):
                #print(type(x))
                #if type(x) == "Tag":
                if x.name == "a":
                    #print(list(x.children))
                    str1 = str1 + " ".join(list(x.children))
                else:
                    #print(x)
                    if str(x) != "<br/>":
                        str1 = str1 + " " + str(x)
                    else:
                        str1 = str1 + "\n"
            str1 = re.sub("&apos;", "'", str1)
            #print("final:" +str1)
            
            str2 = ""       # example
            #print(list(found5[0].children))
            for x in list(found5[0].children):
                if x.name == "a":
                    #print(list(x.children))
                    str2 = str2 + " ".join(list(x.children))
                else:
                    #print(x)
                    if str(x) != "<br/>":
                        str2 = str2 + " " + str(x)
                    else:
                        str2 = str2 + "\n"
            str2 = re.sub("&apos;", "'", str2)
            #print("final:" +str2)
                    
            #print(list(found2[0].children)[0].strip())
            #print(list(list(found3[0].children)[1].children)[0].strip())
            #print(list(found4[0].children)[0].strip())
            #print(list(found5[0].children)[0].strip())
            
            #print("found3")
            #print(list(found3[0].children))
            #print(len(list(found3[0].children)))
            #print(list(list(found3[0].children)[0].children))
            #urboutput = "UrbanDictionary.com Word of the Day ("+list(found2[0].children)[0].strip()+") is: "+list(list(found3[0].children)[0].children)[0].strip()+"\n**Definition**: "+list(found4[0].children)[0].strip()+"\n**Example**: "+list(found5[0].children)[0].strip()
            #for x in found:
            #        return await self.send_message(channel, "The Dictionary.com Word of the Day is: "+x.contents[1].attrs["alt"]+"\n"+dictdefs+link+"\n\n"+urboutput, embed=None)
            #embed = discord.Embed(colour=discord.Colour(0xc27c0e), description="[Dictionary.com]("+link+") Word of the Day is: **"+found[0].contents[1].attrs["alt"]+"**\n"+dictdefs+"\n[UrbanDictionary]("+link1+") Word of the Day is: **"+list(list(found3[0].children)[0].children)[0].strip()+"**\n**Definition**: "+list(found4[0].children)[0].strip()+"\n**Example**: "+list(found5[0].children)[0].strip())
            embed = discord.Embed(color = discord.Color(0xc27c0e), description="[Dictionary.com]("+link+") Word of the Day is: **"+found[0].contents[1].attrs["alt"]+"**\n"+dictdefs+"\n[UrbanDictionary]("+link1+") Word of the Day is: **"+list(list(found3[0].children)[0].children)[0].strip()+"**\n**Definition**: "+str1+"\n**Example**: "+str2)
            embed.set_author(name="Word of the Day")
            embed.set_footer(text="Produced with no care, I hope it worked", icon_url=self.user.avatar_url)
            return await self.send_message(srvr, embed=embed)
        except Exception as e:
            await self.send_message(srvr, "There was an error while getting the word of the day. Here is a link to it:\n"+link)
            #await self.send_message(srvr, e)
    async def _get_urbwordofday(self, srvr):
        print("URBAN WORD OF THE DAY TRIGGERED (6PM)")
        try:
            link = "http://urbandictionary.com/"
            f = requests.get(link, headers={"content-type":"text"})
            soup = bS(f.text, "html.parser")
            found = soup.body.find_all("ribbon", "meaning", "example")
            for x in found:
                print("x:" + x)
                for y in x.contents:
                    print("x.contents: "+y)
        except:
            print("Failed to get the word of the day from urbandictionary.")
    async def cmd_roll(self, message, author, channel):
        '''
        Usage:
            !roll [How many dice]d[Number of sides] [+ Number added to die roll]
            Roll an x sided die y times and add z to it each time. Example: !roll 1d20. Z is optional.
        '''
        finalmsg = ""
        adder = 0
        msgparams = message.content.strip().split()
        msgparams.pop(0)
        random.seed()
        msgparams = " ".join(msgparams).split("d")
        if len(msgparams) != 2 and len(msgparams) != 3:
            return Response("There is an issue with your parameters. Try again using the correct format: !roll xdy [+z]", delete_after=20)
        msgparamsfinal = [msgparams[0]]+msgparams[1].split("+")
        msgparamsfinal[0] = msgparamsfinal[0].strip()
        msgparamsfinal[1] = msgparamsfinal[1].strip()
        try:
            msgparamsfinal[0] = int(msgparamsfinal[0])
            msgparamsfinal[1] = int(msgparamsfinal[1])
        except:
            return Response("You tried so hard and got so far. Try again using the correct format: !roll xdy [+z]",  delete_after=20)
        if len(msgparamsfinal) > 2:
            msgparamsfinal[2] = msgparamsfinal[2].strip()
            msgparamsfinal[2] = int(msgparamsfinal[2])
            adder = 1
        if msgparamsfinal[0] > 10 or msgparamsfinal[1] > 1000000 or msgparamsfinal[1] < 2:
            return Response("Stop.", delete_after=10)
        for x in range(msgparamsfinal[0]):
            if len(msgparamsfinal) < 3:
                roll = random.randint(1,msgparamsfinal[1])
                if roll == 1:
                    finalmsg = finalmsg + str(x+1)+". "+author.name + " rolled a "+str(roll)+" :skull_crossbones::skull: :ghost: RIP :ghost: :skull: :skull_crossbones: \n"
                elif roll == msgparamsfinal[1]:
                    finalmsg = finalmsg + str(x+1)+". "+author.name + " rolled a "+str(roll)+" :eggplant: :peach: :100: <:pant:231177797798854657> <:pant:231177797798854657> :fire: :fire: HOLY FUCK :fire: :fire: <:pant:231177797798854657> <:pant:231177797798854657> :100: :point_right: :ok_hand: \n"
                else:
                    finalmsg = finalmsg + str(x+1)+". "+author.name + " rolled a "+str(roll)+"\n"
            else:
                roll = random.randint(1,msgparamsfinal[1])
                if roll == 1:
                    finalmsg = finalmsg + str(x+1)+". "+author.name + " rolled a "+str(roll)+" + "+str(msgparamsfinal[2])+" = "+str(msgparamsfinal[2]+roll)+" :skull_crossbones::skull: :ghost: RIP :ghost: :skull: :skull_crossbones: \n"
                elif roll == msgparamsfinal[1]:
                    finalmsg = finalmsg + str(x+1)+". "+author.name + " rolled a "+str(roll)+" + "+str(msgparamsfinal[2])+" = "+str(msgparamsfinal[2]+roll)+" HOLY FUCK :ok_hand: \n"
                else:
                    finalmsg = finalmsg + str(x+1)+". "+author.name + " rolled a "+str(roll)+" + "+str(msgparamsfinal[2])+" = "+str(msgparamsfinal[2]+roll)+"\n"
        await self.send_message(channel, finalmsg.strip())
    #@owner_only
    async def cmd_say(self, message, channel):
        '''
        Test command.
        '''
        msg = message.content.strip().split()
        msg.pop(0)
        await self.send_message(channel, " ".join(msg))
    async def cmd_msgblock(self, message, channel, channel_mentions):
        '''
        Usage:
            !msgblock [number of seconds] [#channelname]
            Blocks all messages by everyone except mods and admins in the channel.
            If msgblock is already in effect for the channel, no matter the parameters, the block ends.
        '''
        #check for if self.mblock is on (anywhere)
        #check for if self.mblock is on in the channel
        #end mblock in channel if its on there
        params = message.content.split()
        params.pop(0)
        lengthoftime = 300
        try:
            if int(params[0]) > 0:
                lengthoftime = int(params[0])
            else:
                lengthoftime = 300
        except:
            lengthoftime = 300
        if channel_mentions:
            channel = channel_mentions[0]
        if len(params) == 2:
            try:
                if int(params[1]) > 0:
                    lengthoftime = int(params[1])
                else:
                    lengthoftime = 300
            except:
                print("MESSAGE BLOCK: Parameter check occurred.")
        if channel in self.mblockchanlist:
            self.mblockchanlist.pop(self.mblockchanlist.index(channel))
            return await self.send_message(channel, "Message block for this channel forcibly ended.")
        else:
            self.mblockchanlist.append(channel)
        await self.send_message(channel, "Message block now in effect. Messages will be instantly deleted for the next "+str(lengthoftime)+" seconds.")        
        await self._mblock_controller(channel, tinseconds=lengthoftime)
    async def cmd_linkblock(self, message, channel, channel_mentions):
        '''
        Usage:
            !linkblock [number of seconds] [#channelname]
            Blocks all messages containing links by everyone except mods and admins in the channel.
            If linkblock is already in effect for the channel, no matter the parameters, the block ends.
        '''
        params = message.content.split()
        params.pop(0)
        lengthoftime = 300
        try:
            if int(params[0]) > 0:
                lengthoftime = int(params[0])
            else:
                lengthoftime = 300
        except:
            lengthoftime = 300
        if channel_mentions:
            channel = channel_mentions[0]
        if len(params) == 2:
            try:
                if int(params[1]) > 0:
                    lengthoftime = int(params[1])
                else:
                    lengthoftime = 300
            except:
                print("LINK BLOCK: Parameter check occurred.")
        if channel in self.linkblockchanlist:
            self.linkblockchanlist.pop(self.linkblockchanlist.index(channel))
            return await self.send_message(channel, "Link block for this channel forcibly ended.")
        else:
            self.linkblockchanlist.append(channel)
        await self.send_message(channel, "Link block now in effect. Messages with links or uploads will be instantly deleted for the next "+str(lengthoftime)+" seconds.")
        await self._linkblock_controller(channel, tinseconds=lengthoftime)
    async def cmd_mute(self, server, channel, message, author, user_mentions):
        '''
        Usage:
            !mute @user
            Adds @user to a role which overrides all other roles which has the effect of muting @user from every channel on the server.
            Also as a side effect restricts access to nsfw channels temporarily.
            This command supports multiple users. @user mention in the message is scraped and added to the mute role.
            It will return a list of users which are already muted if they are muted.
        '''
        if len(user_mentions) == 0:
            return Response("You didn't even target a user. Try !mute @user", delete_after=10)
        mutefaillist = []
        muterole = None
        for role in server.roles:
            if role.name == "Muted":
                muterole = role
        if muterole == None:
            return Response("Where's the mute role???", delete_after=5)
        for user in user_mentions: #users are member objects
            if user == author:
                return Response("Hey, you can't mute yourself.", delete_after=5)
            if muterole in user.roles:
                mutefaillist.append(user.name)
            else:
                await self.add_roles(user, muterole)
        if len(mutefaillist) > 0:
            return await self.send_message(channel, "The following users are already muted: "+", ".join(mutefaillist))
        await self.send_message(channel, "I muted them.")
        
    async def cmd_unmute(self, server, channel, message, author, user_mentions):
        '''
        Usage:
            !umute @user
            Removes @user from the mute role.
            Supports a list of @users.
        '''
        if len(user_mentions) == 0:
            return Response("You didn't even target a user. Try !unmute @user", delete_after=10)
        mutefaillist = []
        muterole = None
        for role in server.roles:
            if role.name == "Muted":
                muterole = role
        if muterole == None:
            return Response("Where's the mute role???", delete_after=5)
        for user in user_mentions:
            if user == author:
                return Response("Hey, you can't unmute yourself.", delete_after=5)
            if muterole in user.roles:
                await self.remove_roles(user, muterole)
            else:
                mutefaillist.append(user.name)
        if len(mutefaillist) > 0:
            return await self.send_message(channel, "The following users are already unmuted: "+", ".join(mutefaillist))
        await self.send_message(channel, "I unmuted them.")
        
    async def cmd_activity(self, server, channel, message, author, user_mentions):
        '''
        Usage:
            !activity @user
            Checks the activity for a user as logged by the bot.
            This monitors away, online, do not disturb, and offline activity.
            The time difference given is formatted as: Days, Hours:Minutes:Seconds.
        '''
        if len(user_mentions) == 0:
            return Response("Supply a user with @user.", delete_after=10)
        if user_mentions[0].id not in self.activityDict:
            return Response("I have no data on this user yet. Wait for their status to change.", delete_after=15)
        try:
            await self.delete_message(message)
        except:
            print("Couldn't delete the triggering message")
        dnow = datetime.now()
        dthenarray = self.activityDict[user_mentions[0].id][1].split()
        dthenarray[0] = dthenarray[0].split("/") #[MM,DD,YYYY]
        dthenarray[1] = dthenarray[1].split(":") #[HH,MM,SS]
        print(dthenarray)
        dthen = datetime(int(dthenarray[0][2]), int(dthenarray[0][0]), int(dthenarray[0][1]), hour=int(dthenarray[1][0]), minute=int(dthenarray[1][1]), second=int(dthenarray[1][2]))
        ddiff = dnow-dthen
        match = re.search("([\d+ days, ]*\d+:\d+:\d+)", str(ddiff))
        datediff = match.group(0)
        await self.send_message(channel, "User "+user_mentions[0].name+" went "+self.activityDict[user_mentions[0].id][0]+" at "+self.activityDict[user_mentions[0].id][1].strip()+". That was "+datediff+" ago.\n(I deleted your message, "+author.name+", to cut down on mentions.)")
    
    async def _linkblock_controller(self, lbchan, tinseconds=300):
        await asyncio.wait_for(asyncio.sleep(tinseconds), timeout=tinseconds+5, loop=self.loop)
        if lbchan in self.linkblockchanlist:
            self.linkblockchanlist.pop(self.linkblockchanlist.index(lbchan))
            await self.send_message(lbchan, "Link block has been lifted.")
    async def _mblock_controller(self, mbchan, tinseconds=300):
        #starts timer
        #ends message block after timer
        await asyncio.wait_for(asyncio.sleep(tinseconds), timeout=tinseconds+5, loop=self.loop)
        if mbchan in self.mblockchanlist:
            self.mblockchanlist.pop(self.mblockchanlist.index(mbchan))
            await self.send_message(mbchan, "Message block has been lifted.")
        
    async def cmd_poll(self, message, channel, author):
        '''
        Usage:
            !poll [number of minutes] "Poll Question"
            !vote Answer
            Starts a poll for a number of minutes.
            !pollstop stops the poll.
        '''
        params = message.content.split(" ")
        params.pop(0)
        lengthoftime = 300
        print(params)
        try:
            if float(params[0]) > 0 and len(params) > 1 and int(float(params[0])) < 3600:
                lengthoftime = float(params[0])*60
                params.pop(0)
            else:
                lengthoftime = 300
                params.pop(0)
        except Exception as e:
            lengthoftime = 300
            #print(e)
        if len(params) == 0:
            return Response('Try !poll [number of minutes] "Poll Question"', delete_after=15)
        pollquestion = " ".join(params)
        
        embed = discord.Embed(title=pollquestion, colour=discord.Colour(0xc27c0e), description="Answers:", timestamp=message.timestamp)
        
        embed.set_author(name="Poll! Use !vote to vote.")
        authav = author.avatar_url
        if author.avatar_url == None:
            authav = author.default_avatar_url
        embed.set_footer(text="Expires "+str(float(lengthoftime/60))+" minutes after", icon_url=authav)
        kmsg = await self.send_message(channel, embed=embed)
        self.polls.append([pollquestion, embed, channel, set(), dict(), kmsg])
        await self._poll_timer(channel, tinseconds=lengthoftime)
        #polls = ["pollquestion", Embed, Channel, {voterSet}, {votechoiceDict}, Message]
    async def _poll_timer(self, chan, tinseconds=300):
        await asyncio.wait_for(asyncio.sleep(tinseconds), timeout=tinseconds+5, loop=self.loop)
        for i in range(len(self.polls)):
            poll = self.polls[i]
            if poll[2] == chan:
                embed = poll[1]
                nuembed = discord.Embed(title=embed.title, color=embed.color, description=embed.description, timestamp=embed.timestamp + timedelta(minutes=tinseconds/60))
                nuembed.set_author(name="This poll has ended! Use !poll to start another.")
                nuembed.set_footer(text="Expired at", icon_url=embed.footer.icon_url)
                await self.send_message(chan, "The poll has ended!", embed=nuembed)
                return self.polls.pop(i)
                
    async def cmd_vote(self, message, channel, author):
        '''
        Usage:
            !vote [answer]
            Vote for something in the current channel's poll.
            If the option doesn't exist, a new choice is made under that name.
        '''
        params = message.content.split()
        params.pop(0)
        if len(params) < 1:
            await self.delete_message(message)
            return Response("You can't vote for nothing.", reply=True, delete_after=5)
        goodtogo = False
        for poll in self.polls:
            if channel == poll[2]:
                goodtogo = True
        if goodtogo == False:
            await self.delete_message(message)
            return Response("There is no poll going on in here.", reply=True, delete_after=5)
        response = " ".join(params).lower().capitalize()
        for i in range(len(self.polls)):
            poll = self.polls[i]
            if poll[2] == channel:
                if author not in poll[3]:
                    if response in poll[4]:
                        self.polls[i][4][response] = self.polls[i][4][response] + 1
                        self.polls[i][3].add(author)
                        pi = i
                    else:
                        self.polls[i][4][response] = self.polls[i][4][response] = 1
                        self.polls[i][3].add(author)
                        pi = i
                else:
                    await self.delete_message(message)
                    return Response("You can't vote twice.", reply=True, delete_after=5)
        embed = self.polls[pi][1]
        vtstr = ""
        for k,v in self.polls[pi][4].items():
            vtstr = vtstr+"\n"+k+": "+str(v)
        vtstr.strip()
        nuembed = discord.Embed(title=embed.title, color=embed.color, description="Answers:"+vtstr, timestamp=embed.timestamp)
        nuembed.set_author(name="Poll! Use !vote to vote.")
        nuembed.set_footer(text=embed.footer.text, icon_url=embed.footer.icon_url)
        await self.edit_message(self.polls[pi][5], embed=nuembed)
        self.polls[pi][1] = nuembed
        await self.delete_message(message)
    async def cmd_pollstop(self, channel, author):
        '''
        Usage:
            !pollstop
            Stop the poll running in the channel
        '''
        for poll in self.polls:
            if poll[2] == channel:
                self.polls.pop(self.polls.index(poll))
                return await self.send_message(channel, "Poll stopped.")
        await self.send_message(channel, "I couldn't find a poll running in this channel.")
        
    async def cmd_remind(self, channel, user_mentions, author, message):
        '''
        Usage:
            !remind me/@user x m/h/d Message
            Remind you or @user in x minutes, hours, or days of the Message you input.
            Note: This will not work if the bot is offline. If the reminder passes and the bot comes online, the reminder will be sent.
        '''
        params = message.content.strip().split()
        params.pop(0)
        if len(params) == 0:
            return Response("You can't remind nobody of nothing never. Try !remind me/`@user` x m/h/d Message.", delete_after=15)
        if params[0].lower() != "me" and not(re.search("@", params[0])):
            return Response("You can't remind nobody of something. Try !remind me/`@user` etc... ", delete_after=15)
        try:
            if int(float(params[1])) < 0 or int(float(params[1])) > 1000:
                return Response("You can't remind someone of something in the past or so far in the future. Try another number.", delete_after=15)
        except:
            return Response("Something went wrong processing the number of minutes/hours/days. Try an actual number.", delete_after=15)
        if params[2].lower() not in ["m","h","d"]:
            return Response("You didn't indicate a type after the number.", delete_after=15)
        try:
            if params[3]:
                print("Setting up reminder.")
        except:
            return Response("You didn't indicate a remind message.", delete_after=15)
        if user_mentions:
            remindtargID = user_mentions[0].id
        else:
            remindtargID = author.id
        if params[2].lower() == "m":
            expires = datetime.now() + timedelta(minutes=int(params[1]))
        elif params[2].lower() == "h":
            expires = datetime.now() + timedelta(hours=int(params[1]))
        else:
            expires = datetime.now() + timedelta(days=int(params[1]))
        
        msg = " ".join(params[3:])
        f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/reminders.txt", "a")
        try:
            f.write("\n"+remindtargID+"@!@"+str(expires.month)+"/"+str(expires.day)+"/"+str(expires.year)+" "+str(expires.hour)+":"+str(expires.minute)+"@!@"+msg)
        except:
            msg = re.sub("[^a-zA-Z0-9\,\.\? <>:@\!\#\&]+", "", msg)
            f.write("\n"+remindtargID+"@!@"+str(expires.month)+"/"+str(expires.day)+"/"+str(expires.year)+" "+str(expires.hour)+":"+str(expires.minute)+"@!@"+msg)
        f.close()
        self.reminderlist.append([remindtargID, str(expires.month)+"/"+str(expires.day)+"/"+str(expires.year)+" "+str(expires.hour)+":"+str(expires.minute), msg])
        print(self.reminderlist)
        await self.send_message(channel, "I will be sending a reminder via private message at roughly "+self.reminderlist[len(self.reminderlist)-1][1]+' for "'+msg+'"')
        
    def _remind_checker(self):
        currentNowTime = str(datetime.now().month)+"/"+str(datetime.now().day)+"/"+str(datetime.now().year)+" "+str(datetime.now().hour)+":"+str(datetime.now().minute)
        currentDateTime = [[str(datetime.now().month), str(datetime.now().day), str(datetime.now().year)], [str(datetime.now().hour), str(datetime.now().minute)]]
        for i in range(len(self.reminderlist)):
            reminderflag = 0
            checkDateTime = self.reminderlist[i][1].split()
            checkDateTime[0] = checkDateTime[0].split("/")
            checkDateTime[1] = checkDateTime[1].split(":")
            if self.reminderlist[i][1] == currentNowTime:
                reminderflag = 1
            elif (int(checkDateTime[0][0]) < int(currentDateTime[0][0])):
                reminderflag = 1
            elif (int(checkDateTime[0][0]) == int(currentDateTime[0][0]) and int(checkDateTime[0][1]) < int(currentDateTime[0][1])):
                reminderflag = 1
            elif (int(checkDateTime[0][0]) == int(currentDateTime[0][0]) and int(checkDateTime[0][1]) == int(currentDateTime[0][1]) and int(checkDateTime[0][2]) < int(currentDateTime[0][2])):
                reminderflag = 1
            elif (int(checkDateTime[0][0]) == int(currentDateTime[0][0]) and int(checkDateTime[0][1]) == int(currentDateTime[0][1]) and int(checkDateTime[0][2]) == int(currentDateTime[0][2]) and int(checkDateTime[1][0]) < int(currentDateTime[1][0])):
                reminderflag = 1
            elif (int(checkDateTime[0][0]) == int(currentDateTime[0][0]) and int(checkDateTime[0][1]) == int(currentDateTime[0][1]) and int(checkDateTime[0][2]) == int(currentDateTime[0][2]) and int(checkDateTime[1][0]) == int(currentDateTime[1][0]) and int(checkDateTime[1][1]) < int(currentDateTime[1][1])):
                reminderflag = 1
            if reminderflag == 1:
                self.loop.create_task(self._remind_reminder(self.reminderlist[i]))
        self.loop.call_later(25, self._remind_checker)
            
    async def _remind_reminder(self, rlist):
        try:
            remindclient = discord.utils.find(lambda m: m.id == rlist[0], self.get_all_members())
            await self.send_message(remindclient, "Reminder from "+rlist[1]+":\n"+rlist[2])
        except Exception as e:
            print("I FAILED TO FIND A MEMBER IN THE REMIND LIST.")
            print(e)
        fr = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/reminders.txt", "r")
        lines = fr.readlines()
        fr.close()
        fr = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/reminders.txt", "w")
        self.reminderlist.pop(self.reminderlist.index(rlist))
        fr.write("Line @!@ One.")
        for j in range(len(self.reminderlist)):
            fr.write("\n"+"@!@".join(self.reminderlist[j]))

            
    async def cmd_bigavatar(self, channel, author):
        '''
        Usage:
            !bigavatar
            Returns a direct link to the highest res of your avatar I can find.
        '''
        if author.avatar_url:
            return await self.send_message(channel, "Here: "+author.avatar_url)
        else:
            return await self.send_message(channel, "Here: "+author.default_avatar_url)
        
    async def cmd_counthistory(self, message, channel, author):
        '''
        Usage:
            !counthistory a phrase of words
            Returns a number of times a phrase occurred in the last 10,000 messages in the channel.
        '''
        params = message.content.split()
        params.pop(0)
        if len(params) == 0:
            return Response("You can't search for nothing. It does yield something, but it's not useful. Just try something else.", delete_after=10)
        phrase = " ".join(params)
        phrase = phrase.lower()
        #logs = await self.logs_from(channel, limit=100000)
        count = -1
        editlater = await self.send_message(channel, "This is going to take a little while (It's a lot of work, especially for really old channels!)... I'll edit this message when I'm done. In the meantime, you can run this command as many times as you like. It runs in the background!")
        async for msg in self.logs_from(channel, limit=10000):
        #for msg in logs:
            if phrase in msg.content.lower():
                count = count+msg.content.lower().count(phrase)
        await self.edit_message(editlater, "Found: "+str(count)+" not including you using it right there.")
        #gc.collect()
        
    async def on_message_edit(self, before, after):
        if before.content != after.content and before.author.id not in ["261738076404056064", "303440133850660864", "240206755156590592"]:
            d = difflib.Differ()
            txt1 = before.content.strip().splitlines(1)
            txt2 = after.content.strip().splitlines(1)
            result = list(d.compare(txt1,txt2))
            s = difflib.SequenceMatcher(lambda x: x == " ", before.content, after.content)
            blox = s.get_matching_blocks()
            changeBeforeInsert = []
            changeAfterInsert = []
            changeBeforeDelete = []
            changeAfterDelete = []
            #changeAfterLeave = []
            changeBeforeLeave = []
            changeBeforeReplace = []
            changeAfterReplace = []
            for opcode in s.get_opcodes():
                print(opcode)
                if opcode[0] == "insert":
                    changeBeforeInsert.append((opcode[1],opcode[2]))
                    changeAfterInsert.append((opcode[3],opcode[4]))
                if opcode[0] == "delete":
                    changeBeforeDelete.append((opcode[1],opcode[2]))
                    changeAfterDelete.append((opcode[3],opcode[4]))
                if opcode[0] == "equal":
                    changeBeforeLeave.append((opcode[1],opcode[2]))
                    #changeAfterLeave.append((opcode[3],opcode[4]))
                if opcode[0] == "replace":
                    changeBeforeReplace.append((opcode[1],opcode[2]))
                    changeAfterReplace.append((opcode[3],opcode[4]))
            finalmsg = "\n"
            for i  in range(len(changeBeforeLeave)):
                finalmsg = finalmsg + "\nLeave '"+before.content[changeBeforeLeave[i][0]:changeBeforeLeave[i][1]]+"'."
            for i in range(len(changeBeforeInsert)):
                if len(before.content[changeBeforeInsert[i][0]:changeBeforeInsert[i][1]]) == 0:
                    finalmsg = finalmsg + "\nInsert '"+after.content[changeAfterInsert[i][0]:changeAfterInsert[i][1]]+"'"
            for i in range(len(changeBeforeReplace)):
                    finalmsg = finalmsg + "\nReplace '"+before.content[changeBeforeReplace[i][0]:changeBeforeReplace[i][1]]+"'\n\tWith: '"+after.content[changeAfterReplace[i][0]:changeAfterReplace[i][1]]+"'"
            for i in range(len(changeBeforeDelete)):
                if changeAfterDelete[i][1] == len(before.content):
                    finalmsg = finalmsg + "\nDelete '"+after.content[changeAfterDelete[i][0]:changeAfterDelete[i][1]]+"' from 'after.'"
                else:
                    finalmsg = finalmsg + "\nDelete '"+before.content[changeBeforeDelete[i][0]:changeBeforeDelete[i][1]]+"' from 'before.'"
            if before.attachments:
                attachmntMsg = "containing attachments"
            else:
                attachmntMsg = ""
            await self.send_message(self.alertchan, "EDIT: Message "+attachmntMsg+" by "+before.author.name+" in "+before.channel.name+" was edited at "+str(after.edited_timestamp)+".\nBefore: ```"+re.sub("`", "", before.content)+"``` Changes:```"+finalmsg+"```After:```"+re.sub("`", "", after.content)+"``` \n--------------")
            f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/editedmsg.txt", "a")
            f.write("\n"+re.sub("[^a-zA-Z0-9\,\.\? <>:@\!\#\&]+", "", after.author.name)+" at "+str(after.edited_timestamp)+"\nBefore:\t"+re.sub("[^a-zA-Z0-9\,\.\? <>:@\!\#\&]+", "", before.content)+"\nAfter:\t"+re.sub("[^a-zA-Z0-9\,\.\? <>:@\!\#\&]+", "", after.content))
            f.close()
        for x in before.server.channels:
            if x.id == "238521805227294720":
                pinchannel = x
        if before.pinned and after.pinned or not(before.pinned) and not(after.pinned):
            return ""
        elif not(before.pinned) and after.pinned:
            attchmnts = ""
            if after.attachments:
                attchmnts = after.attachments[0]["url"]
            if after.channel.id != "271151253197815808":
                await self.send_message(pinchannel, after.author.name + " in "+after.channel.name+" on date/time: "+str(after.timestamp)+"UTC:\n"+ before.content+ "\n"+attchmnts)
                await self.unpin_message(after)
        #print(after.embeds)
        #for x in after.attachments:
        #    print(x["url"])
    async def on_message_delete(self, message):
        if message.type != discord.MessageType.pins_add:
            if not (message.content.startswith("^") or message.content.startswith("&") or message.content.startswith("!")):
                if message.author.id not in ["261738076404056064", "303440133850660864", "240206755156590592"]:
                    attachmentlist = []
                    if message.attachments:
                        for attachment in message.attachments:
                            attachmentlist.append(attachment["url"])
                    if len(attachmentlist) > 0:
                        attachments = "\n".join(attachmentlist)
                    else:
                        attachments = ""
                    attachments = "\n"+attachments
                    await self.send_message(self.alertchan, "DELETE: by "+message.author.name+" in "+message.channel.name+".\nTimestamp: "+str(message.timestamp)+".\n\nContents:\n"+message.content+""+attachments+"\n--------------")
                    f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/deletedmsg.txt", "a")
                    f.write("\n"+re.sub("[^a-zA-Z0-9\,\.\? <>:@\!\#\&]+", "", message.author.name)+" at "+str(message.timestamp)+"\n\t"+re.sub("[^a-zA-Z0-9\,\.\? <>:@\!\#\&]+", "", message.content))
                    f.close()
        
    async def on_message(self, message):
        await self.wait_until_ready()
        if message.channel.id == "297850406992609281":
            return ""
        if message.channel.id == "313822977043070987":
            return ""
        message_content = message.content.strip()
        global expired_cdt
        global nxtmsgQ
        #if message.server and message.author != self.user:
        #    if message.channel.id == "249261582532476929":
        #        if message_content == "test":
        #            return await self.delete_message(message)
        #        if expired_cdt == 1:
        #            nxtmsgQ.append(message.author.name + ": " + message_content)
        #            return await self.delete_message(message)
        #        else:
        #            msgtosend = "\n".join(nxtmsgQ)
        #            expired_cdt = 1
        #            self.msgcooldowntimer()
        #            if nxtmsgQ == []:
        #                return ""
        #            nxtmsgQ = []
        #            return await self.send_message(message.channel, msgtosend)
                    
#womwom rip block
        if message.channel in self.mblockchanlist:
            user_permissions = self.permissions.for_user(message.author)
            if user_permissions.name != "Admin" and user_permissions.name != "Owner (auto)":
                await self.delete_message(message)
        if message.channel in self.linkblockchanlist:
            user_permissions = self.permissions.for_user(message.author)
            if user_permissions.name != "Admin" and user_permissions.name != "Owner (auto)":
                if re.search("http", message_content) or re.search("ftp", message_content) or message.attachments:
                    await self.delete_message(message)
        
        if message.type == discord.MessageType.pins_add:
            await self.delete_message(message)
            await self.send_message(message.channel, "A message from this channel has been pinned. I have attempted to move the pin to the pins channel.")
        if message.mention_everyone:
            user_permissions = self.permissions.for_user(message.author)
            if user_permissions.name != "Admin" and user_permissions.name != "Moderator" and user_permissions.name != "Owner (auto)":
                if re.search("@everyone", message_content):
                    await self.delete_message(message)
                    await self.send_message(message.channel, "Sorry, you can't mention everyone at once like that. Try `@here` instead.")
        
            
            
        print(message_content)
        #print(self.messages)
        if message.channel.is_private and message.author.id != "303440133850660864":
            print("Private channel found for message. Checking against new member list")
            if message.author.id in self.newmemberlist:
                for x in self.servers:
                    if x.name == "Ghost Division":
                        srvr = x
                for mbr in x.members:
                    if mbr.id == message.author.id:
                        roler = mbr
                for r in srvr.roles:
                    if r.name == "Regular":
                        regrole = r
                await self.replace_roles(roler, regrole)
                fl = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/idlist.txt", "r")
                lines = fl.readlines()
                fl.close()
                fl = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/idlist.txt", "w")
                for line in lines:
                    if not(re.search(message.author.id, line)):
                        #if line != message.author.id:
                        fl.write(line)
                await self.send_message(message.channel, "Enjoy your stay.")
                return self.newmemberlist.pop(self.newmemberlist.index(message.author.id))
            else:
                return await self.send_message(message.channel, "There is no reason you should pm me right now.")
        try:
            for x in message.server.channels:
                if x.id == "264837364415725568":
                    modchannel = x
            if "faggot" in message_content.lower() and message.author.id == "204801115974402050":
                await self.send_message(modchannel, "'faggot' detected in channel "+message.channel.name)
                await self.send_message(self.alertchan, "'faggot' detected in channel "+message.channel.name)
            if "lol" == message_content.lower() and message.author.id == "204801115974402050":
                flol = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/lol.txt", "r")
                lols = flol.read()
                flol.close()
                flol = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/lol.txt", "w")
                flol.write(str(int(lols)+1))
                flol.close()
                
        except:
            print("The bot received a PM from someone.")
            
        msgwords = message_content.split()
        capped = 0
        if message_content == message_content.upper() and re.search("[A-Z]", message_content):
            if message.author.name == self.cap_msg_nick:
                self.cap_msg_in_a_row = self.cap_msg_in_a_row + 1
                if self.cap_msg_in_a_row > 3:
                    await self.send_message(modchannel, "All caps spam by "+self.cap_msg_nick+" detected in channel "+message.channel.name+" (x"+str(self.cap_msg_in_a_row)+")")
                    await self.send_message(self.alertchan, "CAPS SPAM: "+self.cap_msg_nick+" in "+message.channel.name+" (x"+str(self.cap_msg_in_a_row)+")")
            else:
                self.cap_msg_nick = message.author.name
                self.cap_msg_in_a_row = 1
        else:
            if message.author.name == self.cap_msg_nick:
                self.cap_msg_in_a_row = 0
                self.cap_msg_nick = ""
    #generally accepted sentence format: s v or "implied you" predicate     
        global barquiet
        global freqdict
        global freqlist
        global barsaver
        if (message_content.lower().startswith("bar ") or message_content.lower().startswith("forcebar") or message_content.lower().startswith("bar, ") or message_content.lower().startswith("barbar")) and not message_content.startswith(self.config.command_prefix) and message.author != self.user:
            #wom pull and spit actions here
            global baruse
            if baruse == "stop":
                return ""
            baruse = "stop"
            self.barusetimer()
            
            #f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/wordfreq.txt", "r+")
            msgwords = re.sub("[^a-zA-Z0-9\,\.\? <>:@\!\#\&]+", "", message_content).split()
            forced = 0
            #if msgwords[0] == "forcebar" and message.author.id == "104461925009608704":
            #    forced = 1
            #if forced == 0:
            #    f.close()
            #    return ""
            msgwords.pop(0)
            if msgwords[0] == "awaken" and message.author.id == "104461925009608704" and barquiet == 1:
                barquiet = 0
                global timerun
                timerun.cancel()
                #f.close()
                return await self.send_message(message.channel, "I awaken.")
            if barquiet == 1 and forced == 0:
                #f.close()
                return ""
            if (msgwords[0] == "stfu" or msgwords[0] == "quiet") and barquiet == 0:
                barquiet = 1
                try:
                    if int(msgwords[1])>0:
                        self.barstfutimer(int(msgwords[1]))
                        #f.close()
                        return await self.send_message(message.channel, "bye for "+msgwords[1]+" seconds")
                    self.barstfutimer()
                    #return await self.send_message(message.channel, "bye for 300 seconds")
                    #f.close()
                    return ""
                except:
                    self.barstfutimer()
                    #return await self.send_message(message.channel, "bye for 300 seconds")
                    #f.close()
                    return ""
            
            tmpmsgwrds = msgwords.copy()
            for i in range(len(msgwords)):
                if tmpmsgwrds[i].startswith("http") or tmpmsgwrds[i].startswith("www."):
                    msgwords.remove(tmpmsgwrds[i])
            wordsphrase = list()
            nxtwrphr = ""
            if len(msgwords) > 2:
                for w in msgwords:
                    if random.randint(1,10) > 3:
                        if nxtwrphr == "":
                            nxtwrphr = w
                        else:
                            nxtwrphr = nxtwrphr + " " + w
                    else:
                        if nxtwrphr == "":
                            wordsphrase.append(w)
                        else:
                            wordsphrase.append(nxtwrphr)
                            nxtwrphr = w
                if nxtwrphr != "":
                    wordsphrase.append(nxtwrphr)
                    nxtwrphr = ""
            else:
                wordsphrase = msgwords.copy()
            for w in wordsphrase:
                if w in freqdict:
                    freqdict[w] = str(int(freqdict[w]) + 1)
                else:
                    freqdict[w] = "1"
                freqlist.append(w)
            #for k,v in freqdict.items():
            #    f.write(k+","+str(v)+"\n")
            #f.close()
            #if barsaver != 1:
            #    self.barmemorysavetimer()
            
            
            
            
            nxtmsg = list()
            incmsg = ""
            verbs = ["is", "should", "be", "should be", "isn't", "may be", "can", "may", "could be", "would be", "has", "gets", "is"]
            namelist = ["tox", "poco", "soof", "arteth", "arty", "cody", "mar", "mario", "john", "tails", "guner", "vexx", "redd", "ukrainian", "atanga", "signis", "lazarus", "nansae", "ronwe", "emeris", "relay", "rythoka", "bae", "baewulf", "miri", "demo", "mpra2"]
            if msgwords[0].lower() in namelist and len(msgwords) == 1:
                sndmsg = msgwords[0]
                sndmsg = sndmsg+" "+verbs[random.randint(0,len(verbs)-1)]
                for _ in range(random.randint(1,10)):
                    sndmsg = sndmsg+" "+freqlist[random.randint(0,len(freqlist)-1)]
                return await self.send_message(message.channel, sndmsg)
            if msgwords[0].lower() in namelist and len(msgwords) > 1:
                sndmsg = msgwords[0]
                if msgwords[1] in verbs:
                    sndmsg = sndmsg+" "+msgwords[1]
                added = 0
                for _ in range(random.randint(1,10)):
                    sndmsg = sndmsg+" "+freqlist[random.randint(0,len(freqlist)-1)]
                    if random.randint(1,10) > 3 and added == 0 and msgwords[1] in verbs:
                        sndmsg = sndmsg+" "+" ".join(msgwords[2:])
                        added = 1
                    elif random.randint(1,10) > 3 and added == 0 and msgwords[1] not in verbs:
                        sndmsg = sndmsg+" "+" ".join(msgwords[1:])
                        added = 1
                return await self.send_message(message.channel, sndmsg)
            for _ in range(random.randint(1,random.randint(3,13))):
                nxtmsg.append(freqlist[random.randint(0,len(freqlist)-1)])
            nwmsg = 1
            for x in nxtmsg:
                if random.randint(1,10) > 3 and nwmsg == 1 and len(wordsphrase) > 1:
                    incmsg = incmsg + " " + wordsphrase[random.randint(0,len(wordsphrase)-1)]
                    nwmsg = 0
                if x in punctmrks:
                    incmsg = incmsg + x
                else:
                    incmsg = incmsg + " " + x
            nuincmsg = incmsg.strip().split()
            for i in range(len(nuincmsg)):
                try:
                    if (nuincmsg[i].endswith(".") or nuincmsg[i].endswith("?") or nuincmsg[i].endswith("!")) and len(nuincmsg) > 2:
                        nuincmsg.append(nuincmsg[i])
                        nuincmsg.pop(len(nuincmsg)-2)
                        nuincmsg.remove(nuincmsg[i])
                    if nuincmsg[i].endswith(",") and i == len(nuincmsg)-1:
                        nuincmsg[i] = re.sub("$,", "", nuincmsg[i])
                except:
                    print("ran out of index range")
            sndmsg = ""
            for x in nuincmsg:
                sndmsg = sndmsg + " " + x
            #if forced == 1:
            #    forced = 0
            #    return await self.send_message(message.channel, sndmsg)
            await self.send_message(message.channel, sndmsg)
            
            
        elif not message_content.startswith(self.config.command_prefix) and message.author != self.user and not message_content.startswith("&") and not message_content.startswith("!") and not message.channel.id == "249261582532476929":
            #wom pull and save actions here
            f = open("/home/barinade/Desktop/Discordbots/Ubuntu-nosleep/musicbot/wordfreq.txt", "w")
            msgwords = re.sub("[^a-zA-Z0-9\,\.\? <>:@\!\#\&]+", "", message_content).split()
            tmpmsgwrds = msgwords.copy()
            for i in range(len(msgwords)):
                if tmpmsgwrds[i].startswith("http") or tmpmsgwrds[i].startswith("www."):
                    msgwords.remove(tmpmsgwrds[i])
            wordsphrase = list()
            nxtwrphr = ""
            if len(msgwords) > 2:
                for w in msgwords:
                    if random.randint(1,10) > 3:
                        if nxtwrphr == "":
                            nxtwrphr = w
                        else:
                            nxtwrphr = nxtwrphr + " " + w
                    else:
                        if nxtwrphr == "":
                            wordsphrase.append(w)
                        else:
                            wordsphrase.append(nxtwrphr)
                            nxtwrphr = w
                if nxtwrphr != "":
                    wordsphrase.append(nxtwrphr)
                    nxtwrphr = ""
            else:
                wordsphrase = msgwords.copy()
            for w in wordsphrase:
                if len(w) > 40:
                    print("I skipped a phrase that was too long")
                else:
                    if w in freqdict:
                        freqdict[w] = str(int(freqdict[w]) + 1)
                    else:
                        freqdict[w] = "1"
                    freqlist.append(w)
            for k,v in freqdict.items():
                f.write(k+","+str(v)+"\n")
            f.close()
            #if barsaver != 1:
            #    self.barmemorysavetimer()
            
            
            
#womwom end            
        if not message_content.startswith(self.config.command_prefix):
            return

        if message.author == self.user:
            self.safe_print("Ignoring command from myself (%s)" % message.content)
            return
        if self.config.bound_channels and message.channel.id not in self.config.bound_channels and not message.channel.is_private:
            return  # if I want to log this I just move it under the prefix check

        command, *args = message_content.split()  # Uh, doesn't this break prefixes with spaces in them (it doesn't, config parser already breaks them)
        command = command[len(self.config.command_prefix):].lower().strip()

        handler = getattr(self, 'cmd_%s' % command, None)
        if not handler:
            return

        if message.channel.is_private:
            if not (message.author.id == self.config.owner_id and command == 'joinserver'):
                await self.send_message(message.channel, 'You cannot use this bot in private messages.')
                return

        if message.author.id in self.blacklist and message.author.id != self.config.owner_id:
            self.safe_print("[User blacklisted] {0.id}/{0.name} ({1})".format(message.author, message_content))
            return

        else:
            self.safe_print("[Command] {0.id}/{0.name} ({1})".format(message.author, message_content))

        user_permissions = self.permissions.for_user(message.author)

        argspec = inspect.signature(handler)
        params = argspec.parameters.copy()

        # noinspection PyBroadException
        try:
            if user_permissions.ignore_non_voice and command in user_permissions.ignore_non_voice:
                await self._check_ignore_non_voice(message)

            handler_kwargs = {}
            if params.pop('message', None):
                handler_kwargs['message'] = message

            if params.pop('channel', None):
                handler_kwargs['channel'] = message.channel

            if params.pop('author', None):
                handler_kwargs['author'] = message.author

            if params.pop('server', None):
                handler_kwargs['server'] = message.server

            if params.pop('player', None):
                handler_kwargs['player'] = await self.get_player(message.channel)

            if params.pop('permissions', None):
                handler_kwargs['permissions'] = user_permissions

            if params.pop('user_mentions', None):
                handler_kwargs['user_mentions'] = list(map(message.server.get_member, message.raw_mentions))

            if params.pop('channel_mentions', None):
                handler_kwargs['channel_mentions'] = list(map(message.server.get_channel, message.raw_channel_mentions))

            if params.pop('voice_channel', None):
                handler_kwargs['voice_channel'] = message.server.me.voice_channel

            if params.pop('leftover_args', None):
                handler_kwargs['leftover_args'] = args

            args_expected = []
            for key, param in list(params.items()):
                doc_key = '[%s=%s]' % (key, param.default) if param.default is not inspect.Parameter.empty else key
                args_expected.append(doc_key)

                if not args and param.default is not inspect.Parameter.empty:
                    params.pop(key)
                    continue

                if args:
                    arg_value = args.pop(0)
                    handler_kwargs[key] = arg_value
                    params.pop(key)

            if message.author.id != self.config.owner_id:
                if user_permissions.command_whitelist and command not in user_permissions.command_whitelist:
                    raise exceptions.PermissionsError(
                        "This command is not enabled for your group (%s)." % user_permissions.name,
                        expire_in=20)

                elif user_permissions.command_blacklist and command in user_permissions.command_blacklist:
                    raise exceptions.PermissionsError(
                        "This command is disabled for your group (%s)." % user_permissions.name,
                        expire_in=20)

            if params:
                docs = getattr(handler, '__doc__', None)
                if not docs:
                    docs = 'Usage: {}{} {}'.format(
                        self.config.command_prefix,
                        command,
                        ' '.join(args_expected)
                    )

                docs = '\n'.join(l.strip() for l in docs.split('\n'))
                await self.safe_send_message(
                    message.channel,
                    '```\n%s\n```' % docs.format(command_prefix=self.config.command_prefix),
                    expire_in=60
                )
                return

            response = await handler(**handler_kwargs)
            if response and isinstance(response, Response):
                content = response.content
                if response.reply:
                    content = '%s, %s' % (message.author.mention, content)

                sentmsg = await self.safe_send_message(
                    message.channel, content,
                    expire_in=response.delete_after if self.config.delete_messages else 0,
                    also_delete=message if self.config.delete_invoking else None
                )

        except (exceptions.CommandError, exceptions.HelpfulError, exceptions.ExtractionError) as e:
            print("{0.__class__}: {0.message}".format(e))

            expirein = e.expire_in if self.config.delete_messages else None
            alsodelete = message if self.config.delete_invoking else None

            await self.safe_send_message(
                message.channel,
                '```\n%s\n```' % e.message,
                expire_in=expirein,
                also_delete=alsodelete
            )

        except exceptions.Signal:
            raise

        except Exception:
            traceback.print_exc()
            if self.config.debug_mode:
                await self.safe_send_message(message.channel, '```\n%s\n```' % traceback.format_exc())

    async def on_voice_state_update(self, before, after):
        if not all([before, after]):
            return

        if before.voice_channel == after.voice_channel:
            return

        if before.server.id not in self.players:
            return

        my_voice_channel = after.server.me.voice_channel  # This should always work, right?

        if not my_voice_channel:
            return

        if before.voice_channel == my_voice_channel:
            joining = False
        elif after.voice_channel == my_voice_channel:
            joining = True
        else:
            return  # Not my channel

        moving = before == before.server.me

        auto_paused = self.server_specific_data[after.server]['auto_paused']
        player = await self.get_player(my_voice_channel)

        if after == after.server.me and after.voice_channel:
            player.voice_client.channel = after.voice_channel

        if not self.config.auto_pause:
            return

        if sum(1 for m in my_voice_channel.voice_members if m != after.server.me):
            if auto_paused and player.is_paused:
                print("[config:autopause] Unpausing")
                self.server_specific_data[after.server]['auto_paused'] = False
                player.resume()
        else:
            if not auto_paused and player.is_playing:
                print("[config:autopause] Pausing")
                self.server_specific_data[after.server]['auto_paused'] = True
                player.pause()

    async def on_server_update(self, before:discord.Server, after:discord.Server):
        if before.region != after.region:
            self.safe_print("[Servers] \"%s\" changed regions: %s -> %s" % (after.name, before.region, after.region))

            await self.reconnect_voice_client(after)

if __name__ == '__main__':
    bot = MusicBot()
    bot.run()
